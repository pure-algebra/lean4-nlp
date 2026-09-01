import Nlp.Pipeline.Annotate
import Nlp.Sequence.PosTaggerLemmas

/-!
# Functional and effectful part-of-speech tagging

The pure bridge respects advertised sentence boundaries, while token-only documents decode as one
HMM sequence. The preferred `NLP` boundary validates documents before decoding, retains typed
model and cancellation failures, and schedules corpora by token count while preserving input
order.
-/

namespace Nlp.Sequence.PosTagger

/-- Check exact sentence-end coverage without allocating a list or proof object. -/
@[inline] def sentenceEndsValid (tokenCount : Nat) (sentEnd : Array Nat) : Bool := Id.run do
  if tokenCount = 0 then
    return sentEnd.isEmpty
  if sentEnd.isEmpty then
    return false
  let mut previous := 0
  for ending in sentEnd do
    unless previous < ending && ending ≤ tokenCount do
      return false
    previous := ending
  return previous == tokenCount

/-- Decode sentence slices independently and concatenate their tags in document order. -/
def tagSentences (tagger : PosTagger) (forms : Array String)
    (sentEnd : Array Nat) : Array String :=
  Id.run do
    let mut start := 0
    let mut tags := Array.emptyWithCapacity forms.size
    for stop in sentEnd do
      for tag in tagger.tagForms (forms.extract start stop) do
        tags := tags.push tag
      start := stop
    return tags

/--
Decode advertised sentences independently, retaining a total length-preserving fallback for
malformed sentence boundaries at the pure unchecked boundary.
-/
def tagFormsWithSentences (tagger : PosTagger) (forms : Array String)
    (sentEnd : Array Nat) : Array String :=
  if sentenceEndsValid forms.size sentEnd then
    let tags := tagger.tagSentences forms sentEnd
    if tags.size = forms.size then tags else tagger.tagForms forms
  else
    tagger.tagForms forms

/-- Sentence-aware decoding, including its fallback, always preserves the form count. -/
@[simp] theorem tagFormsWithSentences_size (tagger : PosTagger) (forms : Array String)
    (sentEnd : Array Nat) :
    (tagger.tagFormsWithSentences forms sentEnd).size = forms.size := by
  dsimp [tagFormsWithSentences]
  split
  · split
    · assumption
    · exact tagger.tagForms_size forms
  · exact tagger.tagForms_size forms

/-- Valid sentence segmentation selects the independently decoded sentence result. -/
theorem tagFormsWithSentences_eq_tagSentences (tagger : PosTagger) (forms : Array String)
    (sentEnd : Array Nat) (valid : sentenceEndsValid forms.size sentEnd = true)
    (aligned : (tagger.tagSentences forms sentEnd).size = forms.size) :
    tagger.tagFormsWithSentences forms sentEnd = tagger.tagSentences forms sentEnd := by
  simp [tagFormsWithSentences, valid, aligned]

/-- Add a POS column after statically requiring the token layer. -/
def tagDoc (tagger : PosTagger) (doc : Doc available)
    (_requirements : Sub [.tokens] available := by decide) : Doc (.pos :: available) :=
  let tags :=
    if Layer.sents ∈ available then
      tagger.tagFormsWithSentences doc.forms doc.sentEnd
    else
      tagger.tagForms doc.forms
  { doc with pos := tags }

/-- POS tagging leaves the token count unchanged. -/
@[simp] theorem tagDoc_size (tagger : PosTagger) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    (tagger.tagDoc doc requirements).size = doc.size := by
  rfl

/-- POS tagging produces exactly one tag for every token. -/
@[simp] theorem tagDoc_pos_size (tagger : PosTagger) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    (tagger.tagDoc doc requirements).pos.size = doc.size := by
  simp only [tagDoc]
  split
  · exact tagger.tagFormsWithSentences_size doc.forms doc.sentEnd
  · exact tagger.tagForms_size doc.forms

/-- Pure POS tagging preserves every structural document invariant. -/
theorem tagDoc_wf (tagger : PosTagger) (doc : Doc available) (wellFormed : doc.WF)
    (requirements : Sub [.tokens] available := by decide) :
    (tagger.tagDoc doc requirements).WF := by
  rcases wellFormed with ⟨spans, _priorPos, lemma, ner, dep, parse⟩
  refine ⟨spans, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    simpa only [tagDoc_size] using tagger.tagDoc_pos_size doc requirements
  · simpa [tagDoc, Doc.size] using lemma
  · simpa [tagDoc, Doc.size] using ner
  · simpa [tagDoc, Doc.size] using dep
  · simpa [tagDoc, Doc.size] using parse

/-- Pure POS tagging also preserves token and sentence semantics. -/
theorem tagDoc_semanticWF (tagger : PosTagger) (doc : Doc available)
    (semantic : doc.SemanticWF)
    (requirements : Sub [.tokens] available := by decide) :
    (tagger.tagDoc doc requirements).SemanticWF := by
  refine ⟨tagger.tagDoc_wf doc semantic.1 requirements, ?_, ?_, ?_, ?_⟩
  · intro tokens
    simpa [tagDoc, Doc.TokenWF, Doc.size] using semantic.2.1 (by simpa using tokens)
  · intro sentences
    have priorSentences : Layer.sents ∈ available := by simpa using sentences
    have prior := semantic.2.2.1 priorSentences
    constructor
    · simpa using prior.1
    · simpa [tagDoc, Doc.SentenceWF, Doc.size] using prior.2
  · intro dependency
    have priorDependency : Layer.dep ∈ available := by simpa using dependency
    have prior := semantic.2.2.2.1 priorDependency
    constructor
    · simpa using prior.1
    · simpa [tagDoc, Doc.DependencyWF] using prior.2
  · intro parse
    have priorParse : Layer.parse ∈ available := by simpa using parse
    have prior := semantic.2.2.2.2 priorParse
    refine ⟨?_, ?_, ?_⟩
    · simpa using prior.1
    · simpa using prior.2.1
    · change doc.ParseWF
      exact prior.2.2

/-- Functional, statically indexed POS annotator. -/
def annotator (tagger : PosTagger) : Ann Id [.tokens] [.pos] :=
  Ann.fromPure "pos" fun requirements doc ↦ tagger.tagDoc doc requirements

end Nlp.Sequence.PosTagger

namespace Nlp.NLP

/-- Describe one invalid numeric cost with its exact stored bits. -/
private def invalidPosCostDetail (kind location : String) (value : Float)
    (bits : UInt64) : String :=
  s!"{kind} cost {location} is {reprStr value} (IEEE-754 bits={bits})" ++
    "; costs must be finite, nonnegative, and use positive zero"

/-- Stable rendering for POS model validation failures. -/
def posCompileErrorDetail : Sequence.PosTagger.CompileError → String
  | .zeroTags => "HMM must contain at least one tag"
  | .wordCapacity count =>
      s!"word vocabulary has {count} entries and leaves no UInt32 identifier for OOV input"
  | .tagCapacity count =>
      s!"tag vocabulary has {count} entries and exceeds UInt32 identifier capacity"
  | .invalidDimensions nTags start transitions unknown =>
      s!"HMM dimensions disagree: nTags={nTags}, start={start}, transitions={transitions}, " ++
        s!"unknown={unknown}; expected nTags, nTags*nTags, nTags"
  | .invalidTagCount expected found =>
      s!"tag vocabulary has {found} names; HMM requires exactly {expected}"
  | .emptyWordName index => s!"word name {index} is empty"
  | .duplicateWordName first duplicate name =>
      s!"word name {duplicate} duplicates word name {first}: {repr name}"
  | .emptyTagName index => s!"tag name {index} is empty"
  | .duplicateTagName first duplicate name =>
      s!"tag name {duplicate} duplicates tag name {first}: {repr name}"
  | .invalidStartCost index value bits =>
      invalidPosCostDetail "start" s!"at index {index}" value bits
  | .invalidTransitionCost index value bits =>
      invalidPosCostDetail "transition" s!"at index {index}" value bits
  | .invalidUnknownCost index value bits =>
      invalidPosCostDetail "unknown-word" s!"at index {index}" value bits
  | .invalidEmissionCost key value bits =>
      invalidPosCostDetail "emission" s!"for key {key}" value bits
  | .emissionTagOutOfRange key tag nTags =>
      s!"emission key {key} contains tag {tag}; expected a tag in [0, {nTags})"
  | .emissionWordOutOfRange key word vocabulary =>
      s!"emission key {key} contains word {word}; expected a word in [0, {vocabulary})"

/-- Compile caller-supplied HMM and vocabulary data through the typed effectful boundary. -/
def compilePosTagger (hmm : Sequence.Hmm) (wordNames tagNames : Array String)
    (source : String := "in-memory POS tagger") : NLP Sequence.PosTagger := do
  checkCancelled
  let tagger ←
    match Sequence.PosTagger.compile hmm wordNames tagNames with
    | .ok tagger => pure tagger
    | .error cause => throw <| .modelCorrupt source (posCompileErrorDetail cause)
  checkCancelled
  return tagger

/-- Estimate a named HMM tagger through the typed effectful model boundary. -/
def estimatePosTagger (sentences : Array (Array (String × String)))
    (addK : Float := 1.0) (source : String := "in-memory POS training data") :
    NLP Sequence.PosTagger := do
  checkCancelled
  let tagger ←
    match Sequence.PosTagger.estimate sentences addK with
    | .ok tagger => pure tagger
    | .error cause => throw <| .modelCorrupt source (posCompileErrorDetail cause)
  checkCancelled
  return tagger

/-- Reject structurally or semantically malformed documents before POS decoding. -/
private def validatePosInput (doc : Doc available) : NLP (Doc available) :=
  match doc.checkedSemantic with
  | .ok checked => pure checked
  | .error cause =>
      throw <| .invalidInput "POS tagger input"
        s!"semantic validation failed: {repr cause}"

/-- Tag one checked document through the preferred effectful API. -/
def tag (tagger : Sequence.PosTagger) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Doc (.pos :: available)) := do
  checkCancelled
  let checked ← validatePosInput doc
  let output := tagger.annotator.run requirements checked
  checkCancelled
  return output

/-- Tag a corpus with token-weighted bounded concurrency and stable order. -/
@[inline] def tagMany (tagger : Sequence.PosTagger) (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Doc (.pos :: available))) :=
  traverseArrayWeighted documents Doc.size fun doc ↦ tag tagger doc requirements

/-- Tag a corpus with an explicit minimum token weight per scheduling unit. -/
@[inline] def tagManyWithMinTokens (minTokens : Nat) (tagger : Sequence.PosTagger)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Doc (.pos :: available))) :=
  traverseArrayWeightedWithMinWeight minTokens documents Doc.size fun doc ↦
    tag tagger doc requirements

end Nlp.NLP
