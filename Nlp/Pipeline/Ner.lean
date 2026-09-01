import Nlp.Pipeline.Annotate
import Nlp.Sequence.NerTagger

/-!
# Functional and effectful named-entity recognition

The pure document bridge validates token and sentence structure, decodes advertised sentences
independently, and writes one flat entity class per token. Token-only documents decode as one
sequence. Typed BIO2 paths and mentions remain available from `NerTagger`; `Doc.ner` follows the
CoreNLP-facing convention of entity names such as `PERSON` or `O`. The `NLP` facade adds typed
model failures, sentence-length policy, cooperative cancellation between decoding kernels, and
stable token-weighted corpus traversal.

This module accepts caller-supplied HMM parameters. It does not claim compatibility with Stanford
CoreNLP's pretrained or feature-rich NER models.
-/

namespace Nlp.Sequence.NerTagger

/-- Why a checked document could not be converted into aligned named-entity output. -/
inductive DocumentError where
  | input (cause : Doc.SemanticError)
  | tagging (sentence start stop : Nat) (cause : TagError)
  | resultSize (sentence expected found : Nat)
  | output (cause : Doc.SemanticError)
  deriving Repr

/-- Half-open sentence ranges selected by the layers advertised on a document. -/
def documentRanges (doc : Doc available) : Array (Nat × Nat) := Id.run do
  if Layer.sents ∈ available then
    let mut ranges := Array.emptyWithCapacity doc.sentEnd.size
    let mut start := 0
    for stop in doc.sentEnd do
      ranges := ranges.push (start, stop)
      start := stop
    return ranges
  else if doc.size = 0 then
    return #[]
  else
    return #[(0, doc.size)]

/-- Linear scheduling work for a form-only sequence model. -/
@[inline] def documentWork (doc : Doc available) : Nat :=
  doc.size

/-- Decode checked sentence ranges and concatenate their flat entity classes in order. -/
private def documentClasses (tagger : NerTagger) (doc : Doc available) :
    Except DocumentError (Array String) := do
  let ranges := documentRanges doc
  let encoded := tagger.encodeForms doc.forms
  let mut classes := Array.emptyWithCapacity doc.size
  for sentence in [0:ranges.size] do
    let (start, stop) := ranges[sentence]!
    let sentenceClasses ←
      match tagger.classesEncodedRange encoded start stop with
      | .ok value => pure value
      | .error cause => throw <| .tagging sentence start stop cause
    let expected := stop - start
    if sentenceClasses.size != expected then
      throw <| .resultSize sentence expected sentenceClasses.size
    for entity in sentenceClasses do
      classes := classes.push entity
  return classes

/--
Recognize named entities in a semantically checked document through the pure functional API.

Advertised sentences are independent BIO2 sequences. Without a sentence layer, all tokens form
one sequence. The result contains exactly one flat entity class per token.
-/
def tagDocument (tagger : NerTagger) (doc : Doc available)
    (_requirements : Sub [.tokens] available := by decide) :
    Except DocumentError (Doc (.ner :: available)) := do
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause => throw <| .input cause
  let classes ← tagger.documentClasses checked
  let output : Doc (.ner :: available) := { checked with ner := classes }
  match output.checkedSemantic with
  | .ok value => pure value
  | .error cause => throw <| .output cause

end Nlp.Sequence.NerTagger

namespace Nlp.NLP

/-- Stable detail for one rejected canonical BIO2 spelling. -/
private def bioParseErrorDetail : Sequence.Bio.ParseError → String
  | .emptyEntity label => s!"BIO2 label {repr label} has an empty entity type"
  | .invalidLabel label =>
      s!"{repr label} is not `O`, `B-TYPE`, or `I-TYPE`"

/-- Describe an invalid NER cost with its exact stored bits. -/
private def invalidNerCostDetail (kind location : String) (value : Float)
    (bits : UInt64) : String :=
  s!"{kind} cost {location} is {reprStr value} (IEEE-754 bits={bits})" ++
    "; costs must be finite, nonnegative, and use positive zero"

/-- Stable rendering for the constrained numeric BIO2 model boundary. -/
private def constrainedHmmErrorDetail : Sequence.ConstrainedHmmCompileError → String
  | .stateCapacity count =>
      s!"BIO2 state inventory {count} exceeds the UInt32 identifier capacity"
  | .invalidDimensions nTags start transitions unknown =>
      s!"HMM dimensions disagree: nTags={nTags}, start={start}, transitions={transitions}, " ++
        s!"unknown={unknown}; expected nTags, nTags*nTags, nTags"
  | .invalidTagCount expected found =>
      s!"BIO2 inventory has {found} states; HMM requires exactly {expected}"
  | .duplicateTag first duplicate label =>
      s!"BIO2 state {duplicate} duplicates state {first}: {repr label}"
  | .missingOutside => "BIO2 inventory has no `O` state"
  | .orphanInside index entity =>
      s!"BIO2 state {index} is I-{entity}, but the inventory has no B-{entity} state"
  | .invalidStartCost index value bits =>
      invalidNerCostDetail "start" s!"at index {index}" value bits
  | .invalidTransitionCost index value bits =>
      invalidNerCostDetail "transition" s!"at index {index}" value bits
  | .invalidUnknownCost index value bits =>
      invalidNerCostDetail "unknown-word" s!"at index {index}" value bits
  | .invalidEmissionCost key value bits =>
      invalidNerCostDetail "emission" s!"for key {key}" value bits
  | .emissionTagOutOfRange key tag nTags =>
      s!"emission key {key} contains state {tag}; expected a state in [0, {nTags})"

/-- Stable rendering for failures in the named BIO2 model boundary. -/
def nerCompileErrorDetail : Sequence.NerTagger.CompileError → String
  | .wordCapacity count =>
      s!"word vocabulary has {count} entries and leaves no UInt32 identifier for OOV input"
  | .emptyWordName index => s!"word name {index} is empty"
  | .duplicateWordName first duplicate name =>
      s!"word name {duplicate} duplicates word name {first}: {repr name}"
  | .invalidTagLabel index label cause =>
      s!"BIO2 state label {index} ({repr label}) is invalid: {bioParseErrorDetail cause}"
  | .reservedEntityType index label =>
      s!"BIO2 state label {index} ({repr label}) uses reserved background entity type `O`"
  | .constrained cause => constrainedHmmErrorDetail cause
  | .emissionWordOutOfRange key word vocabulary =>
      s!"emission key {key} contains word {word}; expected a word in [0, {vocabulary})"
  | .emptyTrainingForm sentence token =>
      s!"training sentence {sentence}, token {token} has an empty surface form"
  | .invalidTrainingTag sentence token label cause =>
      s!"training sentence {sentence}, token {token} has invalid label {repr label}: " ++
        bioParseErrorDetail cause
  | .reservedTrainingEntityType sentence token label =>
      s!"training sentence {sentence}, token {token} has label {repr label}; " ++
        "entity type `O` is reserved for background"
  | .illegalTrainingStart sentence token label =>
      s!"training sentence {sentence}, token {token} starts with illegal label {repr label}"
  | .illegalTrainingTransition sentence token prior next =>
      s!"training sentence {sentence}, token {token} has illegal BIO2 transition " ++
        s!"{repr prior} -> {repr next}"

/-- Stable rendering for a defensive failure while extracting typed mentions. -/
private def nerTagErrorDetail : Sequence.NerTagger.TagError → String
  | .invalidState position state stateCount =>
      s!"decoder returned state {state} at token {position}; expected a state in [0, " ++
        s!"{stateCount})"
  | .resultSize start expected found =>
      s!"decoder projection at token {start} returned {found} positions; expected {expected}"
  | .invalidPath (.orphanInside index entity) =>
      s!"I-{entity} at token {index} has no active mention"
  | .invalidPath (.mismatchedInside index expected found) =>
      s!"I-{found} at token {index} continues an active {expected} mention"
  | .invalidPath (.invalidSpan start stop entity) =>
      s!"{entity} mention has invalid half-open span [{start}, {stop})"

/-- Compile a caller-supplied named BIO2 HMM through the typed effectful boundary. -/
def compileNerTagger (hmm : Sequence.Hmm) (wordNames tagLabels : Array String)
    (source : String := "in-memory NER tagger") : NLP Sequence.NerTagger := do
  checkCancelled
  let tagger ←
    match Sequence.NerTagger.compile hmm wordNames tagLabels with
    | .ok value => pure (value.withDiagnosticSource source)
    | .error cause => throw <| .modelCorrupt source (nerCompileErrorDetail cause)
  checkCancelled
  return tagger

/-- Estimate a named BIO2 HMM through the typed effectful model boundary. -/
def estimateNerTagger (sentences : Array (Array (String × String)))
    (addK : Float := 1.0) (source : String := "in-memory NER training data") :
    NLP Sequence.NerTagger := do
  checkCancelled
  let tagger ←
    match Sequence.NerTagger.estimate sentences addK with
    | .ok value => pure (value.withDiagnosticSource source)
    | .error cause => throw <| .modelCorrupt source (nerCompileErrorDetail cause)
  checkCancelled
  return tagger

/-- Apply the configured sentence-length policy before named-entity inference. -/
@[inline] def nerSkipReason? (config : Config) (tokens : Nat) : Option SkipReason :=
  if config.maxLen < tokens then some (.tooLong tokens config.maxLen) else none

/-- Recognize one located document with cancellation boundaries around each sentence kernel. -/
private def tagNamedEntitiesAt (location : String) (tagger : Sequence.NerTagger)
    (doc : Doc available)
    (_requirements : Sub [.tokens] available := by decide) :
    NLP (Analysis (Doc (.ner :: available))) := do
  checkCancelled
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause =>
      throw <| .invalidInput location
        s!"semantic validation failed: {repr cause}"
  let ranges := Sequence.NerTagger.documentRanges checked
  let config := (← read).config
  for range in ranges do
    if let some reason := nerSkipReason? config (range.2 - range.1) then
      return .skipped reason
  let encoded := tagger.encodeForms checked.forms
  checkCancelled
  let mut classes := Array.emptyWithCapacity checked.size
  for sentence in [0:ranges.size] do
    checkCancelled
    let (start, stop) := ranges[sentence]!
    let sentenceClasses ←
      match tagger.classesEncodedRange encoded start stop with
      | .ok value => pure value
      | .error cause =>
        throw <| .modelCorrupt tagger.diagnosticSource <|
          s!"{location}: sentence {sentence} tokens [{start}, {stop}) produced an invalid " ++
            s!"BIO2 path: {nerTagErrorDetail cause}"
    let expected := stop - start
    if sentenceClasses.size != expected then
      throw <| .modelCorrupt tagger.diagnosticSource <|
        s!"{location}: sentence {sentence} tokens [{start}, {stop}) returned " ++
          s!"{sentenceClasses.size} classes; expected {expected}"
    for entity in sentenceClasses do
      classes := classes.push entity
  checkCancelled
  let output : Doc (.ner :: available) := { checked with ner := classes }
  match output.checkedSemantic with
  | .ok value => return .ok value
  | .error cause =>
    throw <| .modelCorrupt tagger.diagnosticSource
      s!"{location}: NER decoding violated its checked document invariant: {repr cause}"

/-- Recognize one document through the checked effectful NER boundary. -/
@[inline] def tagNamedEntities (tagger : Sequence.NerTagger) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Analysis (Doc (.ner :: available))) :=
  tagNamedEntitiesAt "NER tagger input" tagger doc requirements

/-- Recognize a corpus with an explicit minimum token weight per scheduling unit. -/
@[inline] def tagNamedEntitiesManyWithMinTokens (minTokens : Nat)
    (tagger : Sequence.NerTagger) (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Analysis (Doc (.ner :: available)))) :=
  traverseArrayWeightedIndexedWithMinWeight minTokens documents
    Sequence.NerTagger.documentWork fun index doc ↦
      tagNamedEntitiesAt s!"NER tagger input document {index}" tagger doc requirements

/-- Recognize a corpus with bounded token-weighted concurrency and stable input order. -/
@[inline] def tagNamedEntitiesMany (tagger : Sequence.NerTagger)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Analysis (Doc (.ner :: available)))) :=
  traverseArrayWeightedIndexed documents Sequence.NerTagger.documentWork fun index doc ↦
    tagNamedEntitiesAt s!"NER tagger input document {index}" tagger doc requirements

end Nlp.NLP
