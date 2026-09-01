import Nlp.Parse.CompiledCKY
import Nlp.Pipeline.Annotate

/-!
# Effectful compiled parsing

This module is the user-facing effect boundary for compiled CKY. Grammar validation, cancellation,
sentence-length policy, and bounded corpus concurrency live here. The reusable grammar and CKY
kernel remain pure in `Nlp.CompiledCNF` and `Nlp.Parse`.
-/

namespace Nlp.NLP

/-- Human-readable context for a grammar compilation failure. -/
def compileErrorDetail : CompileError → String
  | .nonterminalCapacity count =>
      s!"nonterminal count {count} exceeds the UInt32 identifier capacity {UInt32.size}"
  | .binaryRuleCapacity count =>
      s!"binary rule count {count} exceeds the UInt32 source-index capacity {UInt32.size}"
  | .lexicalRuleCapacity count =>
      s!"lexical rule count {count} exceeds the UInt32 source-index capacity {UInt32.size}"
  | .invalidStart start nNT =>
      s!"start nonterminal {start.toNat} is outside the valid range [0, {nNT})"
  | .invalidBinaryRule source lhs left right nNT =>
      s!"binary rule {source} has nonterminals lhs={lhs.toNat}, left={left.toNat}, " ++
        s!"right={right.toNat}; every nonterminal must be in [0, {nNT})"
  | .invalidLexicalRule source lhs nNT =>
      s!"lexical rule {source} has lhs={lhs.toNat}; it must be in [0, {nNT})"

/-- Adapt a pure grammar validation failure to the typed model-loading failure channel. -/
@[inline] def compileErrorToFail (source : String) (error : CompileError) : Fail :=
  .modelCorrupt source (compileErrorDetail error)

/--
Validate and compile one reusable grammar under an explicit adaptive-index configuration.

`source` is retained in typed failures so callers can identify the model or resource that supplied
the invalid grammar. Cancellation is observed on both sides of the pure compilation boundary.
-/
def compileGrammarWith [Inhabited K] (config : CompileConfig) (grammar : CNF K)
    (source : String := "in-memory CNF grammar") : NLP (CompiledCNF K) := do
  NLP.checkCancelled
  let compiled ←
    match CompiledCNF.compileWith config grammar with
    | .ok value => pure value
    | .error error => throw <| compileErrorToFail source error
  NLP.checkCancelled
  return compiled

/-- Validate and compile one reusable grammar with the production index threshold. -/
@[inline] def compileGrammar [Inhabited K] (grammar : CNF K)
    (source : String := "in-memory CNF grammar") : NLP (CompiledCNF K) :=
  compileGrammarWith CompileConfig.default grammar source

/--
Run the pure compiled CKY chart kernel at a cooperative cancellation boundary.

This low-level effectful entry point intentionally does not apply `Config.maxLen`; callers asking
for a complete chart have opted into its full allocation. `parseSentence` is the policy-aware
user-facing entry point.
-/
def parseChart {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (compiled : CompiledCNF K) (words : Array Tok) : NLP (Array K) := do
  NLP.checkCancelled
  let chart := Parse.ckyCompiled compiled words
  NLP.checkCancelled
  return chart

/--
Parse one sentence and return its start-symbol value.

Sentences beyond `Config.maxLen` are skipped as data. A zero start-symbol value means that the
grammar produced no analysis and is likewise represented as data. Cancellation remains a typed
fatal effect and is checked immediately before and after the pure CKY kernel.
-/
def parseSentence {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (compiled : CompiledCNF K) (words : Array Tok) : NLP (Analysis K) := do
  NLP.checkCancelled
  let limit := (← read).config.maxLen
  if limit < words.size then
    return .skipped (.tooLong words.size limit)
  let value := Parse.ckyCompiledGoal compiled words
  NLP.checkCancelled
  if value == 0 then return .noAnalysis else return .ok value

/--
Parse a corpus with bounded, ordered parallelism and an explicit sentence grain.

The immutable compiled grammar and sentence array are shared read-only. Worker and hard-cap limits
come from `Config`; `minGrain` controls the number of sentences per scheduling unit. Nested fan-out
is suppressed and input order is preserved.
-/
def parseSentencesWithGrain {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (minGrain : Nat) (compiled : CompiledCNF K) (sentences : Array (Array Tok)) :
    NLP (Array (Analysis K)) :=
  NLP.traverseArrayWithGrain minGrain sentences (parseSentence compiled)

/-- Parse a corpus using one expensive CKY sentence as the default scheduling grain. -/
@[inline] def parseSentences {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (compiled : CompiledCNF K) (sentences : Array (Array Tok)) :
    NLP (Array (Analysis K)) :=
  parseSentencesWithGrain 1 compiled sentences

end Nlp.NLP
