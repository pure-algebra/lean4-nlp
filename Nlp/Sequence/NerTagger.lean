import Nlp.Core.Data.Interner
import Nlp.Sequence.ConstrainedHmm

/-!
# Named BIO2 entity tagging

`NerTagger` is the validated named boundary around the numeric constrained-HMM kernel. It keeps
the ordered BIO2 state inventory and exact case-sensitive vocabulary outside the decoding loop.
One word identifier immediately after the vocabulary is reserved for out-of-vocabulary forms;
sparse model emissions are checked not to use that identifier.

Inference returns typed BIO2 tags, their canonical rendered labels, CoreNLP-style flat entity
classes, and validated mentions. Mention spans use half-open token coordinates. Range inference
keeps coordinates relative to the full input array and never allocates a string slice.
-/

namespace Nlp.Sequence

/-- A validated named entity tagger backed by a BIO2-constrained HMM. -/
structure NerTagger where
  private mk ::
  /-- Validated numeric model and compiled BIO2 transition index. -/
  model : ConstrainedHmm
  /-- Exact, case-sensitive vocabulary indexed by numeric observations. -/
  words : Interner
  /-- Reserved observation identifier strictly outside the vocabulary. -/
  oov : Tok
  /-- Caller-supplied model identity retained by effectful diagnostics. -/
  diagnosticSource : String

namespace NerTagger

/-- Why named inputs and a numeric HMM could not form a validated NER model. -/
inductive CompileError where
  /-- The vocabulary leaves no distinct `UInt32` identifier for OOV forms. -/
  | wordCapacity (count : Nat)
  /-- A vocabulary entry is empty. -/
  | emptyWordName (index : Nat)
  /-- A vocabulary spelling occurs at two source positions. -/
  | duplicateWordName (first duplicate : Nat) (name : String)
  /-- An ordered state label is not canonical BIO2. -/
  | invalidTagLabel (index : Nat) (label : String) (cause : Bio.ParseError)
  /-- An entity type collides with the reserved flat background class `O`. -/
  | reservedEntityType (index : Nat) (label : String)
  /-- The constrained numeric model or its BIO2 inventory is invalid. -/
  | constrained (cause : ConstrainedHmmCompileError)
  /-- A sparse emission uses an observation outside the exact vocabulary. -/
  | emissionWordOutOfRange (key : UInt64) (word vocabulary : Nat)
  /-- A supervised observation has an empty surface form. -/
  | emptyTrainingForm (sentence token : Nat)
  /-- A supervised tag is not canonical BIO2. -/
  | invalidTrainingTag (sentence token : Nat) (label : String) (cause : Bio.ParseError)
  /-- A supervised entity type collides with the reserved flat background class `O`. -/
  | reservedTrainingEntityType (sentence token : Nat) (label : String)
  /-- A supervised sentence starts with `I-TYPE`. -/
  | illegalTrainingStart (sentence token : Nat) (label : String)
  /-- A supervised adjacent pair violates BIO2 continuation semantics. -/
  | illegalTrainingTransition (sentence token : Nat) (prior next : String)
deriving Repr

/-- One nonempty entity mention in full-input half-open token coordinates. -/
structure Mention where
  private mk ::
  /-- Inclusive token offset in the full input column. -/
  start : Nat
  /-- Exclusive token offset in the full input column. -/
  stop : Nat
  /-- Exact entity type shared by the mention's `B` and `I` tags. -/
  entity : Bio.EntityType
  /-- Every emitted mention contains at least its `B-TYPE` token. -/
  private nonempty : start < stop
deriving Repr, DecidableEq

/-- Project one typed BIO2 tag to CoreNLP's flat token-level entity class. -/
@[inline] def entityClass : Bio.Tag → String
  | .outside => "O"
  | .begin entity | .inside entity => entity.name

namespace Mention

/-- Every validated mention has a strictly positive half-open width. -/
theorem start_lt_stop (mention : Mention) : mention.start < mention.stop :=
  mention.nonempty

end Mention

/-- Why a typed tag sequence could not be converted into validated mentions. -/
inductive MentionError where
  /-- An `I-TYPE` tag has no active preceding mention. -/
  | orphanInside (index : Nat) (entity : String)
  /-- An `I-TYPE` tag changes the active entity type. -/
  | mismatchedInside (index : Nat) (expected found : String)
  /-- Defensive failure if an active mention would have an empty or reversed span. -/
  | invalidSpan (start stop : Nat) (entity : String)
deriving Repr, DecidableEq

/-- A validated inference result over one normalized range of a full form column. -/
structure Tagging where
  private mk ::
  /-- Inclusive offset of the normalized range in the full input. -/
  start : Nat
  /-- Exclusive offset of the normalized range in the full input. -/
  stop : Nat
  /-- Typed BIO2 output, local to `[start, stop)`. -/
  tags : Array Bio.Tag
  /-- Canonical `O`, `B-TYPE`, and `I-TYPE` spellings. -/
  labels : Array String
  /-- CoreNLP-style flat classes: `O` or the entity type at each token. -/
  classes : Array String
  /-- Validated mentions whose coordinates are relative to the full input. -/
  mentions : Array Mention
  /-- The normalized range is ordered. -/
  private ordered : start ≤ stop
  /-- There is exactly one typed tag per token in the normalized range. -/
  private tagCount : tags.size = stop - start
  /-- Canonical labels stay aligned with typed tags. -/
  private labelCount : labels.size = tags.size
  /-- Flat entity classes stay aligned with typed tags. -/
  private classCount : classes.size = tags.size
  /-- Canonical labels are exactly the rendering of typed tags. -/
  private labelsProjection : labels = tags.map Bio.Tag.render
  /-- Flat classes are exactly the entity projection of typed tags. -/
  private classesProjection : classes = tags.map entityClass
deriving Repr

namespace Tagging

/-- Number of tokens represented by this tagging. -/
@[inline] def size (tagging : Tagging) : Nat := tagging.stop - tagging.start

/-- A tagging's normalized range is ordered. -/
theorem start_le_stop (tagging : Tagging) : tagging.start ≤ tagging.stop :=
  tagging.ordered

/-- Typed output has exactly the tagging's normalized range width. -/
@[simp] theorem tags_size (tagging : Tagging) : tagging.tags.size = tagging.size :=
  tagging.tagCount

/-- Canonical labels have exactly the tagging's normalized range width. -/
@[simp] theorem labels_size (tagging : Tagging) : tagging.labels.size = tagging.size := by
  rw [tagging.labelCount, tagging.tags_size]

/-- Flat entity classes have exactly the tagging's normalized range width. -/
@[simp] theorem classes_size (tagging : Tagging) : tagging.classes.size = tagging.size := by
  rw [tagging.classCount, tagging.tags_size]

/-- Canonical label output is definitionally governed by the typed BIO2 path. -/
@[simp] theorem labels_eq_map (tagging : Tagging) :
    tagging.labels = tagging.tags.map Bio.Tag.render :=
  tagging.labelsProjection

/-- Flat class output is definitionally governed by the typed BIO2 path. -/
@[simp] theorem classes_eq_map (tagging : Tagging) :
    tagging.classes = tagging.tags.map entityClass :=
  tagging.classesProjection

end Tagging

/-- Why constrained decoding could not be exposed as a validated named result. -/
inductive TagError where
  /-- A decoder state ordinal escaped the validated BIO2 inventory. -/
  | invalidState (position state stateCount : Nat)
  /-- A projection unexpectedly changed the number of decoded positions. -/
  | resultSize (start expected found : Nat)
  /-- The decoded typed path did not form legal BIO2 mentions. -/
  | invalidPath (cause : MentionError)
deriving Repr, DecidableEq

/-- Build the canonical dense interner represented by distinct ordered word names. -/
private def buildWords (names : Array String) : Except CompileError Interner := do
  let mut ids : Std.HashMap String UInt32 := Std.HashMap.emptyWithCapacity names.size
  for index in [0:names.size] do
    let name := names[index]!
    if name.isEmpty then
      throw <| .emptyWordName index
    match ids.get? name with
    | some first => throw <| .duplicateWordName first.toNat index name
    | none => ids := ids.insert name (UInt32.ofNat index)
  return { ids, names }

/-- Parse an ordered inventory without changing its source order. -/
private def parseTags (labels : Array String) : Except CompileError (Array Bio.Tag) := do
  let mut tags := Array.emptyWithCapacity labels.size
  for index in [0:labels.size] do
    let label := labels[index]!
    match Bio.Tag.parse label with
    | .ok tag =>
        match tag with
        | .begin entity | .inside entity =>
            if entity.name == "O" then
              throw <| .reservedEntityType index label
        | .outside => pure ()
        tags := tags.push tag
    | .error cause => throw <| .invalidTagLabel index label cause
  return tags

/-- Recover the packed word coordinate of one sparse emission key. -/
@[inline] def emissionWord (key : UInt64) : Tok :=
  key.toUInt32

/-- Select the lowest-key out-of-vocabulary sparse emission deterministically. -/
private def validateEmissionWords (hmm : Hmm) (vocabulary : Nat) : Except CompileError Unit := do
  let mut first : Option (UInt64 × Nat) := none
  for (key, _) in hmm.emit do
    let word := (emissionWord key).toNat
    if !(word < vocabulary) then
      match first with
      | none => first := some (key, word)
      | some (priorKey, _) =>
        if key < priorKey then
          first := some (key, word)
  match first with
  | some (key, word) => throw <| .emissionWordOutOfRange key word vocabulary
  | none => pure ()

/--
Validate exact word names and canonical ordered BIO2 labels around a numeric HMM.

`wordNames[i]` names observation `i`; `tagLabels[i]` names state `i`. The reserved OOV identifier
is `wordNames.size`, and compilation rejects every sparse emission outside the vocabulary.
-/
def compile (hmm : Hmm) (wordNames tagLabels : Array String) : Except CompileError NerTagger :=
  if _wordCapacity : wordNames.size < UInt32.size then do
    let words ← buildWords wordNames
    let tags ← parseTags tagLabels
    let model ←
      match ConstrainedHmm.compile hmm tags with
      | .ok value => pure value
      | .error cause => throw <| .constrained cause
    validateEmissionWords hmm wordNames.size
    return .mk model words (UInt32.ofNat wordNames.size) "in-memory NER tagger"
  else
    .error <| .wordCapacity wordNames.size

/-- Adapt word-vocabulary capacity exhaustion during supervised estimation. -/
private def wordInternerError : Interner.Error → CompileError
  | .capacityExceeded limit => .wordCapacity limit

/-- Adapt BIO-state capacity exhaustion during supervised estimation. -/
private def tagInternerError : Interner.Error → CompileError
  | .capacityExceeded limit => .constrained (.stateCapacity limit)

/-- Intern a training form while preserving the model's typed capacity error. -/
private def internWord (words : Interner) (form : String) :
    Except CompileError (Interner × UInt32) :=
  match words.intern form with
  | .ok result => .ok result
  | .error cause => .error (wordInternerError cause)

/-- Intern a canonical training label while preserving BIO-state capacity errors. -/
private def internTag (tags : Interner) (label : String) :
    Except CompileError (Interner × UInt32) :=
  match tags.intern label with
  | .ok result => .ok result
  | .error cause => .error (tagInternerError cause)

/-- Parse one training label and retain its sentence and token coordinates on failure. -/
private def parseTrainingTag (sentence token : Nat) (label : String) :
    Except CompileError Bio.Tag :=
  match Bio.Tag.parse label with
  | .ok tag => do
      match tag with
      | .begin entity | .inside entity =>
          if entity.name == "O" then
            throw <| .reservedTrainingEntityType sentence token label
      | .outside => pure ()
      return tag
  | .error cause => .error (.invalidTrainingTag sentence token label cause)

/-- Check a parsed training tag against the preceding BIO2 state. -/
private def validateTrainingTransition (sentence token : Nat) (prior : Option Bio.Tag)
    (tag : Bio.Tag) : Except CompileError Unit :=
  match prior with
  | none =>
      unless tag.legalStart do
        throw <| .illegalTrainingStart sentence token tag.render
  | some previous =>
      unless Bio.Tag.legalTransition previous tag do
        throw <| .illegalTrainingTransition sentence token previous.render tag.render

/--
Estimate and validate a named constrained HMM from supervised BIO2 sentences.

Training observations are `(surface form, canonical BIO2 label)` pairs. Word and state IDs follow
deterministic first-occurrence order. Invalid labels and illegal BIO2 edges report exact sentence
and token coordinates. `addK` follows `Hmm.estimate`'s normalization policy.
-/
def estimate (sentences : Array (Array (String × String))) (addK : Float := 1.0) :
    Except CompileError NerTagger := do
  let mut words := Interner.empty
  let mut tags := Interner.empty
  let mut encoded := Array.emptyWithCapacity sentences.size
  for sentenceIndex in [0:sentences.size] do
    let sentence := sentences[sentenceIndex]!
    let mut encodedSentence := Array.emptyWithCapacity sentence.size
    let mut prior : Option Bio.Tag := none
    for tokenIndex in [0:sentence.size] do
      let (form, label) := sentence[tokenIndex]!
      if form.isEmpty then
        throw <| .emptyTrainingForm sentenceIndex tokenIndex
      let tag ← parseTrainingTag sentenceIndex tokenIndex label
      validateTrainingTransition sentenceIndex tokenIndex prior tag
      let (nextWords, word) ← internWord words form
      words := nextWords
      let (nextTags, state) ← internTag tags label
      tags := nextTags
      encodedSentence := encodedSentence.push (word, state.toNat)
      prior := some tag
    encoded := encoded.push encodedSentence
  compile (Hmm.estimate encoded tags.size addK) words.names tags.names

/-- Number of compiled BIO2 states. -/
@[inline] def nStates (tagger : NerTagger) : Nat :=
  tagger.model.nStates

/-- Ordered exact vocabulary retained by the tagger. -/
@[inline] def wordNames (tagger : NerTagger) : Array String :=
  tagger.words.names

/-- Replace only the diagnostic model identity retained for effectful failures. -/
def withDiagnosticSource (tagger : NerTagger) (source : String) : NerTagger :=
  .mk tagger.model tagger.words tagger.oov source

/-- Ordered canonical BIO2 state labels retained by the tagger. -/
def tagLabels (tagger : NerTagger) : Array String :=
  tagger.model.tags.map Bio.Tag.render

/-- Encode one form exactly, using the reserved OOV observation when absent. -/
@[inline] def encode (tagger : NerTagger) (form : String) : Tok :=
  (tagger.words.lookup? form).getD tagger.oov

/-- Encode a full form column once for zero-slice range decoding. -/
def encodeForms (tagger : NerTagger) (forms : Array String) : Array Tok :=
  forms.map tagger.encode

/-- Form encoding preserves the full input length. -/
@[simp] theorem encodeForms_size (tagger : NerTagger) (forms : Array String) :
    (tagger.encodeForms forms).size = forms.size := by
  simp [encodeForms]

/-- Normalized width of a half-open range over a form column. -/
def rangeLength (forms : Array String) (start stop : Nat) : Nat :=
  let upper := min stop forms.size
  upper - min start upper

/-- Decode an encode-once full column over a half-open range without allocating a slice. -/
@[inline] def decodeEncodedRange (tagger : NerTagger) (words : Array Tok)
    (start stop : Nat) : Array Nat :=
  tagger.model.decodeRange words start stop

/-- Encode a full form column and decode its normalized half-open range. -/
@[inline] def decodeRange (tagger : NerTagger) (forms : Array String)
    (start stop : Nat) : Array Nat :=
  tagger.decodeEncodedRange (tagger.encodeForms forms) start stop

/-- Decode a complete form column into dense BIO2 state ordinals. -/
@[inline] def decodeForms (tagger : NerTagger) (forms : Array String) : Array Nat :=
  tagger.decodeRange forms 0 forms.size

/-- Range decoding returns exactly its normalized number of form positions. -/
@[simp] theorem decodeRange_size (tagger : NerTagger) (forms : Array String)
    (start stop : Nat) :
    (tagger.decodeRange forms start stop).size = rangeLength forms start stop := by
  simp [decodeRange, decodeEncodedRange, rangeLength, ConstrainedHmm.rangeLength]

/-- Complete named decoding returns one state per form. -/
@[simp] theorem decodeForms_size (tagger : NerTagger) (forms : Array String) :
    (tagger.decodeForms forms).size = forms.size := by
  rw [decodeForms, decodeRange_size]
  simp [rangeLength]

/-- Resolve one dense decoder state without silently substituting an entity label. -/
@[inline] private def checkedTag (tagger : NerTagger) (position state : Nat) :
    Except TagError Bio.Tag :=
  match tagger.model.tags[state]? with
  | some tag => .ok tag
  | none => .error <| .invalidState position state tagger.model.tags.size

/-- Validate one BIO2 edge while projecting a decoded state sequence. -/
private def validatePathStep (prior : Option Bio.Tag) (position : Nat)
    (next : Bio.Tag) : Except TagError Unit :=
  match prior, next with
  | none, .inside entity =>
      .error <| .invalidPath (.orphanInside position entity.name)
  | some .outside, .inside entity =>
      .error <| .invalidPath (.orphanInside position entity.name)
  | some (.begin expected), .inside found
  | some (.inside expected), .inside found =>
      if expected.name == found.name then
        .ok ()
      else
        .error <| .invalidPath (.mismatchedInside position expected.name found.name)
  | _, _ => .ok ()

/-- Bounds-check and validate decoded states while building one caller-selected projection. -/
@[inline] private def projectStates (tagger : NerTagger) (states : Array Nat)
    (offset : Nat) (initial : α) (push : α → Bio.Tag → α) : Except TagError α := do
  let mut output := initial
  let mut prior : Option Bio.Tag := none
  for index in [0:states.size] do
    let tag ← tagger.checkedTag (offset + index) states[index]!
    validatePathStep prior (offset + index) tag
    output := push output tag
    prior := some tag
  return output

/--
Validate dense decoded states and project them to flat entity classes.

The offset affects error coordinates only. The returned array remains local to the supplied state
sequence.
-/
def classesFromStates (tagger : NerTagger) (states : Array Nat) (offset : Nat := 0) :
    Except TagError (Array String) :=
  tagger.projectStates states offset (Array.emptyWithCapacity states.size) fun classes tag ↦
    classes.push (entityClass tag)

/-- Close one active mention at an exclusive full-input offset. -/
private def closeMention (mentions : Array Mention)
    (active : Option (Nat × Bio.EntityType)) (stop : Nat) :
    Except MentionError (Array Mention) :=
  match active with
  | none => .ok mentions
  | some (start, entity) =>
      if nonempty : start < stop then
        .ok <| mentions.push (.mk start stop entity nonempty)
      else
        .error <| .invalidSpan start stop entity.name

/--
Validate a typed BIO2 sequence and extract nonempty half-open entity mentions.

`offset` is added to every local token coordinate, allowing sentence-range results to retain
full-document coordinates. Exact entity boundaries come from `B-TYPE` tags, not flat classes.
-/
def extractMentions (tags : Array Bio.Tag) (offset : Nat := 0) :
    Except MentionError (Array Mention) := do
  let mut mentions : Array Mention := #[]
  let mut active : Option (Nat × Bio.EntityType) := none
  for index in [0:tags.size] do
    let position := offset + index
    match (tags[index]?).getD Bio.Tag.outside with
    | .outside =>
        mentions ← closeMention mentions active position
        active := none
    | .begin entity =>
        mentions ← closeMention mentions active position
        active := some (position, entity)
    | .inside entity =>
        match active with
        | none => throw <| .orphanInside position entity.name
        | some (_, expected) =>
            unless expected.name == entity.name do
              throw <| .mismatchedInside position expected.name entity.name
  closeMention mentions active (offset + tags.size)

/-- Build a rich named result from checked dense states and a normalized range. -/
private def taggingFromStates (tagger : NerTagger) (states : Array Nat)
    (lower upper : Nat) (ordered : lower ≤ upper) : Except TagError Tagging := do
  let tags ←
    tagger.projectStates states lower (Array.emptyWithCapacity states.size) fun tags tag ↦
      tags.push tag
  let mentions ←
    match extractMentions tags lower with
    | .ok value => pure value
    | .error cause => throw <| .invalidPath cause
  let labels := tags.map Bio.Tag.render
  let classes := tags.map entityClass
  if tagCount : tags.size = upper - lower then
    return .mk lower upper tags labels classes mentions ordered tagCount (by simp [labels])
      (by simp [classes]) (by simp [labels]) (by simp [classes])
  else
    throw <| .resultSize lower (upper - lower) tags.size

/-- A successful checked state projection retains its declared normalized range width. -/
private theorem taggingFromStates_size_of_ok (tagger : NerTagger) (states : Array Nat)
    (lower upper : Nat) (ordered : lower ≤ upper) (tagging : Tagging)
    (success : taggingFromStates tagger states lower upper ordered = .ok tagging) :
    tagging.size = upper - lower := by
  cases projected : tagger.projectStates states lower
      #[] (fun tags tag ↦ tags.push tag) with
  | error cause =>
      simp [taggingFromStates, projected, bind, Except.bind] at success
  | ok tags =>
      cases extracted : extractMentions tags lower with
      | error cause =>
          simp [taggingFromStates, projected, extracted, bind, Except.bind] at success
      | ok mentions =>
          by_cases count : tags.size = upper - lower
          · simp [taggingFromStates, projected, extracted, count, bind, Except.bind,
              pure, Except.pure] at success
            cases success
            rfl
          · simp [taggingFromStates, projected, extracted, count, bind, Except.bind,
              pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at success

/-- Convert dense decoded states to a checked named result over an encode-once range. -/
def tagEncodedRange (tagger : NerTagger) (words : Array Tok) (start stop : Nat) :
    Except TagError Tagging :=
  let upper := min stop words.size
  let lower := min start upper
  tagger.taggingFromStates (tagger.decodeEncodedRange words lower upper) lower upper
    (Nat.min_le_right start upper)

/--
Project one encode-once range directly to flat entity classes.

This path retains dense-state and BIO2 validation but avoids allocating typed tags, canonical
labels, and mentions when a document consumer only needs its `ner` column.
-/
def classesEncodedRange (tagger : NerTagger) (words : Array Tok) (start stop : Nat) :
    Except TagError (Array String) := do
  let upper := min stop words.size
  let lower := min start upper
  let states := tagger.decodeEncodedRange words lower upper
  tagger.classesFromStates states lower

/-- Project a form range directly to flat entity classes. -/
def classesRange (tagger : NerTagger) (forms : Array String) (start stop : Nat) :
    Except TagError (Array String) :=
  tagger.classesEncodedRange (tagger.encodeForms forms) start stop

/-- Project a complete form column directly to flat entity classes. -/
@[inline] def classesForms (tagger : NerTagger) (forms : Array String) :
    Except TagError (Array String) :=
  tagger.classesRange forms 0 forms.size

/-- Tag a normalized range of a full form column without allocating a string slice. -/
def tagRange (tagger : NerTagger) (forms : Array String) (start stop : Nat) :
    Except TagError Tagging :=
  tagger.tagEncodedRange (tagger.encodeForms forms) start stop

/-- Tag a complete form column and return all typed and named projections. -/
@[inline] def tagForms (tagger : NerTagger) (forms : Array String) : Except TagError Tagging :=
  tagger.tagRange forms 0 forms.size

/-- A successful range tagging has exactly the normalized requested width. -/
theorem tagRange_size_of_ok (tagger : NerTagger) (forms : Array String)
    (start stop : Nat) (tagging : Tagging)
    (success : tagger.tagRange forms start stop = .ok tagging) :
    tagging.size = rangeLength forms start stop := by
  let words := tagger.encodeForms forms
  let upper := min stop words.size
  let lower := min start upper
  have projected := tagger.taggingFromStates_size_of_ok
    (tagger.decodeEncodedRange words lower upper) lower upper
    (Nat.min_le_right start upper) tagging (by
      simpa [tagRange, tagEncodedRange, words, upper, lower] using success)
  simpa [rangeLength, words, upper, lower] using projected

/-- A successful complete tagging has exactly one result per input form. -/
theorem tagForms_size_of_ok (tagger : NerTagger) (forms : Array String)
    (tagging : Tagging) (success : tagger.tagForms forms = .ok tagging) :
    tagging.size = forms.size := by
  have normalized := tagger.tagRange_size_of_ok forms 0 forms.size tagging (by
    simpa [tagForms] using success)
  simpa [rangeLength] using normalized

end NerTagger

end Nlp.Sequence
