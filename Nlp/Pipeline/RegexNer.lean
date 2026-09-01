import Nlp.Pattern.RegexNer
import Nlp.Pipeline.Annotate

/-!
# Functional RegexNER through the effectful pipeline

The pure `RegexNerModel` owns checked compilation and sentence-range rewriting. This module adds
the preferred `NLP` application boundary: stable typed diagnostics, cooperative cancellation,
per-sentence length policy, and ordered token-weighted corpus traversal.

The surface exposes typed regular token patterns and exact token phrases. It is not a parser for
the Stanford TokensRegex textual language.
-/

namespace Nlp.NLP

open Pattern

/-- Stable rendering for bounded Thompson-automaton compilation failures. -/
private def regularPatternCompileErrorDetail : CompileError → String
  | .ruleBudget required limit =>
      s!"regular rules need {required} entries but the model limit is {limit}"
  | .ruleCapacity count =>
      s!"regular rule count {count} exceeds the UInt32 identifier capacity"
  | .stateBudget required limit =>
      s!"regular automata need {required} states but the model limit is {limit}"
  | .stateCapacity count =>
      s!"regular automata state count {count} exceeds the UInt32 identifier capacity"
  | .edgeBudget required limit =>
      s!"regular automata need {required} edges but the model limit is {limit}"

/-- Stable rendering for bounded exact-phrase compilation failures. -/
private def phraseCompileErrorDetail : PhraseCompileError → String
  | .ruleBudget required limit =>
      s!"exact-phrase rules need {required} entries but the model limit is {limit}"
  | .ruleCapacity count =>
      s!"exact-phrase rule count {count} exceeds the UInt32 identifier capacity"
  | .emptyPhrase rule => s!"exact-phrase lane rule {rule} is empty"
  | .emptyToken rule token =>
      s!"exact-phrase lane rule {rule}, token {token} is empty"
  | .wordCapacity count =>
      s!"exact-phrase vocabulary {count} exceeds the UInt32 identifier capacity"
  | .sourceTokenBudget required limit =>
      s!"exact-phrase sources contain {required} tokens but the model limit is {limit}"
  | .nodeBudget required limit =>
      s!"exact-phrase automata need {required} trie nodes but the model limit is {limit}"
  | .nodeCapacity count =>
      s!"exact-phrase trie node count {count} exceeds the UInt32 identifier capacity"

/-- Stable rendering for the checked mixed-lane RegexNER model boundary. -/
def regexNerCompileErrorDetail : RegexNerCompileError → String
  | .ruleBudget required limit =>
      s!"RegexNER sources contain {required} rules but the model limit is {limit}"
  | .payloadBudget required limit =>
      s!"RegexNER sources retain {required} payload entries but the model limit is {limit}"
  | .sourceByteBudget required limit =>
      s!"RegexNER sources reference {required} UTF-8 bytes but the model limit is {limit}"
  | .emptyEntity rule => s!"RegexNER rule {rule} has an empty entity class"
  | .reservedEntity rule =>
      s!"RegexNER rule {rule} emits reserved background class `O`"
  | .invalidPriority rule value bits =>
      s!"RegexNER rule {rule} has non-finite priority {reprStr value} " ++
        s!"(IEEE-754 bits={bits})"
  | .emptyPhrase rule => s!"RegexNER rule {rule} has an empty exact phrase"
  | .emptyPhraseToken rule token =>
      s!"RegexNER rule {rule}, exact-phrase token {token} is empty"
  | .regular cause => regularPatternCompileErrorDetail cause
  | .phrase cause => phraseCompileErrorDetail cause

/-- Compile a RegexNER model under explicit regular and phrase allocation policies. -/
def compileRegexNerModelWith (config : RegexNerCompileConfig)
    (rules : Array RegexNerRule)
    (source : String := "in-memory RegexNER rules") : NLP RegexNerModel := do
  checkCancelled
  let compiled := RegexNerModel.compileWith config rules
  checkCancelled
  match compiled with
  | .ok value => return value.withDiagnosticSource source
  | .error cause => throw <| .modelCorrupt source (regexNerCompileErrorDetail cause)

/-- Compile a RegexNER model with the default allocation policies. -/
@[inline] def compileRegexNerModel (rules : Array RegexNerRule)
    (source : String := "in-memory RegexNER rules") : NLP RegexNerModel :=
  compileRegexNerModelWith {} rules source

/-- Apply runtime sentence-length policy before RegexNER matching. -/
@[inline] def regexNerSkipReason? (config : Config) (tokens : Nat) : Option SkipReason :=
  if config.maxLen < tokens then some (.tooLong tokens config.maxLen) else none

/-- Stable name for one dynamically required document layer. -/
private def regexNerLayerName : Layer → String
  | .tokens => "tokens"
  | .sents => "sentences"
  | .pos => "part of speech"
  | .lemma => "lemma"
  | .ner => "named entity"
  | .dep => "dependency"
  | .parse => "constituency parse"

/-- Translate a post-validation range failure to a typed model-integrity failure. -/
private def regexNerRangeFail (model : RegexNerModel) (location : String)
    (sentence start stop : Nat) (cause : RegexNerDocumentError) : Fail :=
  let detail :=
    match cause with
    | .invalidLaneRule lane rule available =>
        let laneName := match lane with
          | .regular => "regular"
          | .phrase => "exact-phrase"
        s!"{laneName} lane returned rule {rule}; only {available} rules are available"
    | .classAlignment expected found =>
        s!"class column has {found} entries; expected {expected}"
    | .searchWorkBudget required limit =>
        s!"regular-pattern work bound is {required}; configured limit is {limit}"
    | .candidateBudget required limit =>
        s!"matching attempted candidate {required}; configured limit is {limit}"
    | .invalidRegularSearch rules =>
        s!"overlapping search unexpectedly rejected {rules.size} nullable rules"
    | .input input => s!"unexpected repeated input validation failure: {repr input}"
    | .missingLayer layer =>
        s!"unexpected missing {regexNerLayerName layer} layer after validation"
    | .output output => s!"unexpected intermediate output failure: {repr output}"
  .modelCorrupt model.diagnosticSource <|
    s!"{location}: sentence {sentence} tokens [{start}, {stop}): {detail}"

/-- Rewrite one located document with cancellation around every sentence-local matcher. -/
private def regexNerAt (location : String) (model : RegexNerModel)
    (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Analysis (Doc (.ner :: available))) := do
  checkCancelled
  let validated := model.validateDocument doc requirements
  checkCancelled
  let checked ←
    match validated with
    | .ok value => pure value
    | .error (.input cause) =>
        throw <| .invalidInput location s!"semantic validation failed: {repr cause}"
    | .error (.missingLayer layer) =>
        throw <| .invalidInput location <|
          s!"RegexNER rules require the {regexNerLayerName layer} layer"
    | .error cause =>
        throw <| .modelCorrupt model.diagnosticSource <|
          s!"{location}: document validation reached an impossible state: {repr cause}"
  let ranges := checked.sentenceRanges
  let config := (← read).config
  for range in ranges do
    if let some reason := regexNerSkipReason? config (range.2 - range.1) then
      return .skipped reason
  let mut classes := RegexNerModel.initialClasses checked
  for sentence in [0:ranges.size] do
    checkCancelled
    let (start, stop) := ranges[sentence]!
    let rewritten := RegexNerModel.rewriteRange checked classes start stop
    checkCancelled
    match rewritten with
    | .ok value => classes := value
    | .error (.searchWorkBudget required limit) =>
        return .skipped (.workLimit required limit)
    | .error (.candidateBudget required limit) =>
        return .skipped (.candidateLimit required limit)
    | .error cause => throw <| regexNerRangeFail model location sentence start stop cause
  let assembled := RegexNerModel.assembleDocument checked classes
  checkCancelled
  match assembled with
  | .ok output => return .ok output
  | .error (.classAlignment expected found) =>
      throw <| .modelCorrupt model.diagnosticSource <|
        s!"{location}: final class column has {found} entries; expected {expected}"
  | .error (.output cause) =>
      throw <| .modelCorrupt model.diagnosticSource <|
        s!"{location}: RegexNER rewriting violated its checked document invariant: {repr cause}"
  | .error cause =>
      throw <| .modelCorrupt model.diagnosticSource <|
        s!"{location}: document assembly reached an impossible state: {repr cause}"

/-- Rewrite one checked document through the preferred effectful RegexNER boundary. -/
@[inline] def regexNer (model : RegexNerModel) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Analysis (Doc (.ner :: available))) :=
  regexNerAt "RegexNER input" model doc requirements

/-- Rewrite a corpus with an explicit minimum token weight per scheduling unit. -/
@[inline] def regexNerManyWithMinTokens (minTokens : Nat) (model : RegexNerModel)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Analysis (Doc (.ner :: available)))) :=
  traverseArrayWeightedIndexedWithMinWeight minTokens documents Doc.size fun index doc ↦
    regexNerAt s!"RegexNER input document {index}" model doc requirements

/-- Rewrite a corpus with bounded token-weighted concurrency and stable input order. -/
@[inline] def regexNerMany (model : RegexNerModel) (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Analysis (Doc (.ner :: available)))) :=
  traverseArrayWeightedIndexed documents Doc.size fun index doc ↦
    regexNerAt s!"RegexNER input document {index}" model doc requirements

end Nlp.NLP
