import Nlp.Parse.Unary
import Nlp.Pipeline.Viterbi

/-!
# Effectful unary-aware Viterbi parsing

`UnaryViterbiModel` composes bounded acyclic unary elimination, adaptive Viterbi compilation, and
exact source-tree restoration. The model also exposes a pure functional compile-and-parse surface;
`NLP` adds typed failures, cooperative cancellation, sentence policy, and ordered bounded batches.
-/

namespace Nlp

/-- A failure while compiling a source treebank grammar for restored Viterbi parsing. -/
inductive UnaryViterbiCompileError where
  /-- Structural, cyclic, representation, or expansion-policy rejection. -/
  | elimination (cause : UnaryElimError)
  /-- A source binary rule has a noncanonical probability weight. -/
  | invalidBinaryWeight (source : Nat) (value : Float) (bits : UInt64)
  /-- A source unary rule has a noncanonical probability weight. -/
  | invalidUnaryWeight (source : Nat) (value : Float) (bits : UInt64)
  /-- A source lexical rule has a noncanonical probability weight. -/
  | invalidLexicalWeight (source : Nat) (value : Float) (bits : UInt64)
  /-- Expanded CNF validation or Viterbi numerical validation failed. -/
  | viterbi (cause : ViterbiCompileError)
deriving Repr

/-- A source-locked unary closure paired with its adaptive one-best parser. -/
structure UnaryViterbiModel where
  private mk ::
  /-- Exact unary expansion and restoration provenance. -/
  closed : UnaryFreeGrammar Vit
  /-- Validated adaptive parser for `closed.grammar`. -/
  parser : ViterbiModel
  /-- Caller-supplied model identity retained for invariant-failure diagnostics. -/
  diagnosticSource : String

namespace UnaryViterbiModel

private def validateSourceWeights (grammar : TreebankGrammar Vit) :
    Except UnaryViterbiCompileError Unit := do
  for source in [0:grammar.binary.size] do
    let value := grammar.binary[source]!.w.toFloat
    unless ViterbiModel.isCanonicalWeight value do
      throw <| .invalidBinaryWeight source value value.toBits
  for source in [0:grammar.unary.size] do
    let value := grammar.unary[source]!.w.toFloat
    unless ViterbiModel.isCanonicalWeight value do
      throw <| .invalidUnaryWeight source value value.toBits
  for source in [0:grammar.lexical.size] do
    let value := grammar.lexical[source]!.w.toFloat
    unless ViterbiModel.isCanonicalWeight value do
      throw <| .invalidLexicalWeight source value value.toBits

/--
Build a pure restored-parser model with explicit unary and adaptive-index policies.

Source weights are checked before path expansion. Expanded binary and lexical weights are checked
again by `ViterbiModel`, including products introduced by unary elimination.
-/
def compileWith (unaryConfig : UnaryElimConfig) (indexConfig : CompileConfig)
    (grammar : TreebankGrammar Vit) : Except UnaryViterbiCompileError UnaryViterbiModel := do
  let plan ←
    match grammar.prepareAcyclicUnaryWith unaryConfig with
    | .ok value => pure value
    | .error cause => throw <| .elimination cause
  validateSourceWeights plan.source
  let closed ←
    match plan.execute with
    | .ok value => pure value
    | .error cause => throw <| .elimination cause
  let parser ←
    match ViterbiModel.compileWith indexConfig closed.grammar with
    | .ok value => pure value
    | .error cause => throw <| .viterbi cause
  return .mk closed parser "in-memory treebank grammar"

/-- Build a pure restored-parser model with production unary and index policies. -/
@[inline] def compile (grammar : TreebankGrammar Vit) :
    Except UnaryViterbiCompileError UnaryViterbiModel :=
  compileWith UnaryElimConfig.default CompileConfig.default grammar

/-- Parse to the exact emitted derivation through the pure functional API. -/
@[inline] def derivation? (model : UnaryViterbiModel) (words : Array Tok) :
    Option Parse.Viterbi.Derivation :=
  model.parser.derivation? words

/-- Restore one exact emitted derivation to the original unbinarized treebank space. -/
@[inline] def restoreDerivation? (model : UnaryViterbiModel)
    (derivation : Parse.Viterbi.Derivation) : Option Tree :=
  model.closed.restoreViterbi? derivation

/-- Parse and exactly restore through the pure functional API. -/
def parse? (model : UnaryViterbiModel) (words : Array Tok) : Option Tree :=
  (model.derivation? words).bind model.restoreDerivation?

private def withDiagnosticSource (model : UnaryViterbiModel)
    (source : String) : UnaryViterbiModel :=
  .mk model.closed model.parser source

end UnaryViterbiModel

namespace NLP

/-- Render every unary-elimination rejection with its exact resource or source ordinal. -/
def unaryElimErrorDetail : UnaryElimError → String
  | .nonterminalCapacity count =>
      s!"nonterminal count {count} exceeds the UInt32 identifier capacity {UInt32.size}"
  | .nonterminalBudget required limit =>
      s!"unary elimination needs {required} nonterminals but the limit is {limit}"
  | .unaryRuleBudget required limit =>
      s!"unary elimination needs {required} unary rules but the limit is {limit}"
  | .invalidStart start nNT =>
      s!"start nonterminal {start.toNat} is outside the valid range [0, {nNT})"
  | .invalidBinaryRule source lhs left right nNT =>
      s!"binary rule {source} has nonterminals lhs={lhs.toNat}, left={left.toNat}, " ++
        s!"right={right.toNat}; every nonterminal must be in [0, {nNT})"
  | .invalidUnaryRule source lhs rhs nNT =>
      s!"unary rule {source} has lhs={lhs.toNat}, rhs={rhs.toNat}; " ++
        s!"both nonterminals must be in [0, {nNT})"
  | .invalidLexicalRule source lhs nNT =>
      s!"lexical rule {source} has lhs={lhs.toNat}; it must be in [0, {nNT})"
  | .cycle nonterminals sourceRules =>
      s!"unary cycle nodes={reprStr nonterminals} sourceRules={reprStr sourceRules}"
  | .pathBudget required limit =>
      s!"unary expansion needs {required} paths but the limit is {limit}"
  | .pathRuleVisitBudget required limit =>
      s!"unary expansion needs {required} path-rule visits but the limit is {limit}"
  | .pathLengthBudget required limit =>
      s!"unary expansion needs path length {required} but the limit is {limit}"
  | .outputBinaryBudget required limit =>
      s!"unary expansion needs {required} binary outputs but the limit is {limit}"
  | .outputLexicalBudget required limit =>
      s!"unary expansion needs {required} lexical outputs but the limit is {limit}"
  | .outputRuleBudget required limit =>
      s!"unary expansion needs {required} total outputs but the limit is {limit}"
  | .outputBinaryCapacity count =>
      s!"expanded binary count {count} exceeds the UInt32 rule capacity {UInt32.size}"
  | .outputLexicalCapacity count =>
      s!"expanded lexical count {count} exceeds the UInt32 rule capacity {UInt32.size}"

private def unaryWeightCause (value : Float) (bits : UInt64) : String :=
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

/-- Render a restored-parser compilation failure without erasing source-rule identity. -/
def unaryViterbiCompileErrorDetail : UnaryViterbiCompileError → String
  | .elimination cause => unaryElimErrorDetail cause
  | .invalidBinaryWeight source value bits =>
      s!"binary rule {source} has invalid source Viterbi weight {reprStr value} " ++
        s!"(IEEE-754 bits={bits}); {unaryWeightCause value bits}"
  | .invalidUnaryWeight source value bits =>
      s!"unary rule {source} has invalid source Viterbi weight {reprStr value} " ++
        s!"(IEEE-754 bits={bits}); {unaryWeightCause value bits}"
  | .invalidLexicalWeight source value bits =>
      s!"lexical rule {source} has invalid source Viterbi weight {reprStr value} " ++
        s!"(IEEE-754 bits={bits}); {unaryWeightCause value bits}"
  | .viterbi cause => viterbiCompileErrorDetail cause

/-- Adapt pure restored-parser validation to a path-aware typed model failure. -/
@[inline] def unaryViterbiCompileErrorToFail (source : String)
    (error : UnaryViterbiCompileError) : Fail :=
  .modelCorrupt source (unaryViterbiCompileErrorDetail error)

/-- Compile a restored Viterbi model under explicit unary and adaptive-index policies. -/
def compileUnaryViterbiModelWith (unaryConfig : UnaryElimConfig)
    (indexConfig : CompileConfig) (grammar : TreebankGrammar Vit)
    (source : String := "in-memory treebank grammar") : NLP UnaryViterbiModel := do
  checkCancelled
  let model ←
    match UnaryViterbiModel.compileWith unaryConfig indexConfig grammar with
    | .ok value => pure (value.withDiagnosticSource source)
    | .error error => throw <| unaryViterbiCompileErrorToFail source error
  checkCancelled
  return model

/-- Compile a restored Viterbi model with production unary and index policies. -/
@[inline] def compileUnaryViterbiModel (grammar : TreebankGrammar Vit)
    (source : String := "in-memory treebank grammar") : NLP UnaryViterbiModel :=
  compileUnaryViterbiModelWith .default .default grammar source

/-- Parse one sentence and restore its exact unary and n-ary source-tree structure. -/
def parseUnaryTree (model : UnaryViterbiModel) (words : Array Tok) : NLP (Analysis Tree) := do
  checkCancelled
  let config := (← read).config
  if let some reason := chartSkipReason? config model.parser.grammar.nNT words.size then
    return .skipped reason
  let derivation := model.derivation? words
  checkCancelled
  match derivation with
  | none => return .noAnalysis
  | some value =>
    let restored := model.restoreDerivation? value
    checkCancelled
    match restored with
    | some tree => return .ok tree
    | none =>
      throw <| .modelCorrupt model.diagnosticSource
        "exact emitted derivation failed source-provenance restoration"

/-- Parse restored trees with explicit grain, bounded concurrency, and stable order. -/
def parseUnaryTreesWithGrain (minGrain : Nat) (model : UnaryViterbiModel)
    (sentences : Array (Array Tok)) : NLP (Array (Analysis Tree)) :=
  traverseArrayWithGrain minGrain sentences (parseUnaryTree model)

/-- Parse restored trees with one expensive sentence per scheduling grain. -/
@[inline] def parseUnaryTrees (model : UnaryViterbiModel)
    (sentences : Array (Array Tok)) : NLP (Array (Analysis Tree)) :=
  parseUnaryTreesWithGrain 1 model sentences

end NLP
end Nlp
