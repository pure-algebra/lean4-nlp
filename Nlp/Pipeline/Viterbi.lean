import Nlp.Parse.CompiledViterbi
import Nlp.Pipeline.Parse

/-!
# Effectful one-best constituency parsing

`ViterbiModel` is the reusable validated boundary around the adaptive compiled Viterbi parser.
The functional constructor validates a `CNF Vit` and its numerical domain while selecting a dense
or sparse pair index. The `NLP` facade adds typed failures, cancellation, sentence-length policy,
and bounded ordered batches. Callers that deliberately need operational behavior for
noncanonical floats can still use the lower-level pure kernels directly.
-/

namespace Nlp

/-- A typed Viterbi-model failure produced before any derived index becomes observable. -/
inductive ViterbiCompileError where
  /-- Structural or identifier validation failed. -/
  | grammar (cause : CompileError)
  /-- A source binary production has a noncanonical probability weight. -/
  | invalidBinaryWeight (source : Nat) (value : Float) (bits : UInt64)
  /-- A source lexical production has a noncanonical probability weight. -/
  | invalidLexicalWeight (source : Nat) (value : Float) (bits : UInt64)
deriving Repr

/-- A validated Viterbi grammar whose derived binary index is built exactly once. -/
structure ViterbiModel where
  private mk ::
  /-- Immutable parser data shared by all sentence analyses. -/
  compiled : CompiledCNF Vit

namespace ViterbiModel

private def negativeZeroBits : UInt64 := 0x8000000000000000

/-- The local numerical predicate required by the Viterbi correctness contract. -/
@[inline] def isCanonicalWeight (value : Float) : Bool :=
  value.isFinite && decide (0.0 ≤ value) && decide (value ≤ 1.0) &&
    value.toBits != negativeZeroBits

private def validateWeights (grammar : CNF Vit) : Except ViterbiCompileError Unit := do
  for source in [0:grammar.bin.size] do
    let value := grammar.bin[source]!.w.toFloat
    unless isCanonicalWeight value do
      throw <| .invalidBinaryWeight source value value.toBits
  for source in [0:grammar.lex.size] do
    let value := grammar.lex[source]!.w.toFloat
    unless isCanonicalWeight value do
      throw <| .invalidLexicalWeight source value value.toBits

/-- Validate a Viterbi grammar and derive an adaptive reusable parser model. -/
def compileWith (config : CompileConfig) (grammar : CNF Vit) :
    Except ViterbiCompileError ViterbiModel := do
  let checked ←
    match CompiledCNF.checkSource grammar with
    | .ok value => pure value
    | .error cause => throw <| .grammar cause
  validateWeights grammar
  return ⟨CompiledCNF.compileCheckedWith config checked⟩

/-- Validate and compile with the production adaptive-index threshold. -/
@[inline] def compile (grammar : CNF Vit) : Except ViterbiCompileError ViterbiModel :=
  compileWith CompileConfig.default grammar

/-- The validated source grammar retained by the parser model. -/
@[inline] def grammar (model : ViterbiModel) : CNF Vit :=
  model.compiled.grammar

/-- Produce the exact one-best derivation through the pure functional model API. -/
def derivation? (model : ViterbiModel) (words : Array Tok) :
    Option Parse.Viterbi.Derivation :=
  let chart := Parse.Viterbi.ckyVitCompiled model.compiled words
  Parse.Viterbi.extractCompiledDerivation model.compiled words chart

/-- Produce the ordinary one-best tree through the pure functional model API. -/
def parse? (model : ViterbiModel) (words : Array Tok) : Option Tree :=
  (model.derivation? words).map Parse.Viterbi.Derivation.toTree

end ViterbiModel

namespace NLP

private def floatBitsHex (bits : UInt64) : String :=
  "0x" ++ (BitVec.ofNat 64 bits.toNat).toHex

private def invalidWeightCause (value : Float) (bits : UInt64) : String :=
  if !value.isFinite then
    "weight must be finite"
  else if bits == 0x8000000000000000 then
    "negative zero is not canonical; use +0.0"
  else if decide (value < 0.0) then
    "weight must be nonnegative"
  else if decide (1.0 < value) then
    "weight must not exceed 1.0"
  else
    "weight must be a canonical finite value in [0, 1]"

private def invalidWeightDetail (kind : String) (source : Nat) (value : Float)
    (bits : UInt64) : String :=
  s!"{kind} rule {source} has invalid Viterbi weight {reprStr value} " ++
    s!"(IEEE-754 bits={floatBitsHex bits}); {invalidWeightCause value bits}"

/-- Render a Viterbi compilation failure without losing structural or float provenance. -/
def viterbiCompileErrorDetail : ViterbiCompileError → String
  | .grammar cause => compileErrorDetail cause
  | .invalidBinaryWeight source value bits =>
      invalidWeightDetail "binary" source value bits
  | .invalidLexicalWeight source value bits =>
      invalidWeightDetail "lexical" source value bits

/-- Adapt pure Viterbi validation to a path-aware typed model failure. -/
def viterbiCompileErrorToFail (source : String) : ViterbiCompileError → Fail
  | .grammar cause => compileErrorToFail source cause
  | error => .modelCorrupt source (viterbiCompileErrorDetail error)

/-- Compile a reusable Viterbi model with an explicit adaptive-index configuration. -/
def compileViterbiModelWith (config : CompileConfig) (grammar : CNF Vit)
    (source : String := "in-memory Viterbi grammar") : NLP ViterbiModel := do
  checkCancelled
  let model ←
    match ViterbiModel.compileWith config grammar with
    | .ok value => pure value
    | .error error => throw <| viterbiCompileErrorToFail source error
  checkCancelled
  return model

/-- Compile a validated reusable Viterbi model with the production index threshold. -/
@[inline] def compileViterbiModel (grammar : CNF Vit)
    (source : String := "in-memory Viterbi grammar") : NLP ViterbiModel :=
  compileViterbiModelWith CompileConfig.default grammar source

/--
Produce the one-best tree for a sentence through the preferred effectful API.

Over-length sentences and grammars with no complete derivation are analysis data. Cancellation is
checked before policy inspection and after the pure chart-and-extraction boundary.
-/
def parseTree (model : ViterbiModel) (words : Array Tok) : NLP (Analysis Tree) := do
  checkCancelled
  let config := (← read).config
  if let some reason := chartSkipReason? config model.grammar.nNT words.size then
    return .skipped reason
  let tree := model.parse? words
  checkCancelled
  match tree with
  | some value => return .ok value
  | none => return .noAnalysis

/--
Parse sentences with an explicit item grain, bounded parallelism, and stable input order.

Worker count and dedicated-thread caps still come from `Config`; this argument changes only how
many sentence items the scheduler assigns to one unit of work. Zero is normalized to one.
-/
def parseTreesWithGrain (minGrain : Nat) (model : ViterbiModel)
    (sentences : Array (Array Tok)) :
    NLP (Array (Analysis Tree)) :=
  traverseArrayWithGrain minGrain sentences (parseTree model)

/-- Parse sentences using the cost-informed default of one expensive CKY item per grain. -/
@[inline] def parseTrees (model : ViterbiModel) (sentences : Array (Array Tok)) :
    NLP (Array (Analysis Tree)) :=
  parseTreesWithGrain 1 model sentences

end NLP

end Nlp
