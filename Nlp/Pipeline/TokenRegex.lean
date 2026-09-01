import Nlp.Pattern.TokenRegex
import Nlp.Pipeline.Annotate

/-!
# Functional TokensRegex through the effectful pipeline

The pure `Pattern.TokenRegex` front end retains source provenance and compiles into the existing
bounded token automaton. This module translates compilation, document, resource, and cancellation
outcomes at the preferred `NLP` boundary without moving effects into the matching hot loop.
-/

namespace Nlp.NLP

open Pattern

/-- Stable name for one dynamically required TokensRegex document column. -/
private def tokenRegexLayerName : Layer → String
  | .tokens => "tokens"
  | .sents => "sentences"
  | .pos => "part of speech"
  | .lemma => "lemma"
  | .ner => "named entity"
  | .dep => "dependency"
  | .parse => "constituency parse"

/-- Stable description of one intentionally unsupported textual feature. -/
private def unsupportedTokenRegexFeature : TokenRegex.UnsupportedFeature → String
  | .capturingGroup => "capturing groups"
  | .anchor => "sequence anchors"
  | .regexLiteral => "slash-delimited character regex literals"
  | .reluctantQuantifier => "reluctant quantifiers"
  | .backreference => "capture backreferences"
  | .macro => "macro references"
  | .action => "actions or staged rules"

/-- Stable description of one byte-spanned TokensRegex parse failure. -/
def tokenRegexParseErrorDetail (error : TokenRegex.ParseError) : String :=
  let location := s!"pattern bytes [{error.span.start}, {error.span.stop})"
  let detail :=
    match error.kind with
    | .sourceByteBudget required limit =>
        s!"source needs {required} UTF-8 bytes but the limit is {limit}"
    | .lexemeBudget required limit =>
        s!"scanner needs {required} lexical items but the limit is {limit}"
    | .nestingBudget required limit =>
        s!"parser nesting needs depth {required} but the limit is {limit}"
    | .expandedNodeBudget required limit =>
        s!"lowering needs {required} regular nodes but the limit is {limit}"
    | .unterminatedString => "quoted exact value is unterminated"
    | .invalidEscape => "quoted exact value uses an unsupported escape"
    | .unsupported feature =>
        s!"{unsupportedTokenRegexFeature feature} are not supported by TokensRegex Core 1"
    | .unknownField field => s!"unknown token column {repr field}"
    | .invertedRepeat lower upper =>
        s!"repetition lower bound {lower} exceeds upper bound {upper}"
    | .emptyPattern => "pattern is empty"
    | .expected description => s!"expected {description}"
  s!"{location}: {detail}"

/-- Stable description of one bounded Thompson compilation failure. -/
private def tokenRegexAutomatonErrorDetail : Pattern.CompileError → String
  | .ruleBudget required limit =>
      s!"automaton needs {required} rules but the limit is {limit}"
  | .ruleCapacity count => s!"rule count {count} exceeds compact identifier capacity"
  | .stateBudget required limit =>
      s!"automaton needs {required} states but the limit is {limit}"
  | .stateCapacity count => s!"state count {count} exceeds compact identifier capacity"
  | .edgeBudget required limit =>
      s!"automaton needs {required} edges but the limit is {limit}"

/-- Stable description of one checked textual compilation failure. -/
def tokenRegexCompileErrorDetail : TokenRegex.CompileError → String
  | .parse cause => tokenRegexParseErrorDetail cause
  | .automaton cause => tokenRegexAutomatonErrorDetail cause

/-- Parse and compile one textual token language under explicit allocation policies. -/
def compileTokenRegexWith (parseConfig : TokenRegex.ParseConfig)
    (automatonConfig : Pattern.CompileConfig) (source : String)
    (diagnosticSource : String := "in-memory TokensRegex pattern") :
    NLP TokenRegex.Compiled := do
  checkCancelled
  let compiled := TokenRegex.compileWith parseConfig automatonConfig source
  checkCancelled
  match compiled with
  | .ok value => return value
  | .error cause =>
      throw <| .modelCorrupt diagnosticSource (tokenRegexCompileErrorDetail cause)

/-- Parse and compile one textual token language under production allocation policies. -/
@[inline] def compileTokenRegex (source : String)
    (diagnosticSource : String := "in-memory TokensRegex pattern") :
    NLP TokenRegex.Compiled :=
  compileTokenRegexWith {} {} source diagnosticSource

/-- Match one document range with explicit automaton work and result policies. -/
def matchTokenRegexAtWith (location : String) (searchConfig : Pattern.SearchConfig)
    (compiled : TokenRegex.Compiled) (doc : Doc available)
    (start : Nat := 0) (stop : Nat := doc.size) : NLP (Analysis (Array Pattern.Match)) := do
  checkCancelled
  let result := compiled.findOverlappingRangeWith searchConfig doc start stop
  checkCancelled
  match result with
  | .ok found => return .ok found
  | .error (.input cause) =>
      throw <| .invalidInput location s!"semantic validation failed: {repr cause}"
  | .error (.missingLayer layer) =>
      throw <| .invalidInput location
        s!"pattern requires the advertised {tokenRegexLayerName layer} layer"
  | .error (.search (.workBudget required limit)) =>
      return .skipped (.workLimit required limit)
  | .error (.search (.matchBudget required limit)) =>
      return .skipped (.candidateLimit required limit)
  | .error (.search (.nullableRules rules)) =>
      throw <| .modelCorrupt compiled.source
        s!"overlapping search unexpectedly rejected nullable rules {repr rules}"

/-- Match one document range with production automaton search policies. -/
@[inline] def matchTokenRegex (compiled : TokenRegex.Compiled) (doc : Doc available)
    (start : Nat := 0) (stop : Nat := doc.size) : NLP (Analysis (Array Pattern.Match)) :=
  matchTokenRegexAtWith "TokensRegex input" {} compiled doc start stop

/--
Match a corpus with explicit per-document search policy and minimum scheduling work.

Results retain input order. Scheduling weights use the same conservative automaton work bound
that guards each pure search.
-/
def matchTokenRegexManyWithMinWork (minWork : Nat) (searchConfig : Pattern.SearchConfig)
    (compiled : TokenRegex.Compiled) (documents : Array (Doc available)) :
    NLP (Array (Analysis (Array Pattern.Match))) :=
  let weight := fun doc : Doc available ↦
    compiled.automaton.overlapWorkUpperBound doc.size 0 doc.size
  traverseArrayWeightedIndexedWithMinWeight minWork documents weight fun index doc ↦
    matchTokenRegexAtWith s!"TokensRegex input document {index}" searchConfig compiled doc

/-- Match a corpus with production search and bounded work-balanced concurrency policies. -/
@[inline] def matchTokenRegexMany (compiled : TokenRegex.Compiled)
    (documents : Array (Doc available)) : NLP (Array (Analysis (Array Pattern.Match))) :=
  let weight := fun doc : Doc available ↦
    compiled.automaton.overlapWorkUpperBound doc.size 0 doc.size
  traverseArrayWeightedIndexed documents weight fun index doc ↦
    matchTokenRegexAtWith s!"TokensRegex input document {index}" {} compiled doc

end Nlp.NLP
