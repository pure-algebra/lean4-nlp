import Nlp.Sequence.NerTagger

namespace NlpTests.Sequence.NerTagger

open Nlp Nlp.Sequence
open Nlp.Sequence.Bio

private def cost (value : Float) : Cost := ⟨value⟩

/-- A fixture helper whose fallback is unreachable for canonical labels. -/
private def parsed (label : String) : Tag :=
  match Tag.parse label with
  | .ok tag => tag
  | .error _ => .outside

private def labels : Array String :=
  #["O", "B-PERSON", "I-PERSON", "B-ORGANIZATION", "I-ORGANIZATION"]

private def words : Array String :=
  #["Alice", "Smith", "at", "Acme"]

/-- Dense fixture emissions with one unique best BIO state for each known form. -/
private def fixtureEmissions : Std.HashMap UInt64 Cost := Id.run do
  let mut emissions : Std.HashMap UInt64 Cost := {}
  for tag in [0:labels.size] do
    for word in [0:words.size] do
      let target := match word with
        | 0 => 1
        | 1 => 2
        | 2 => 0
        | _ => 3
      let value := if tag == target then 0.0 else 20.0
      emissions := emissions.insert (Hmm.emissionKey tag (UInt32.ofNat word)) (cost value)
  return emissions

private def numeric : Hmm where
  nTags := labels.size
  start := Array.replicate labels.size (cost 0.0)
  trans := Array.replicate (labels.size * labels.size) (cost 0.0)
  emit := fixtureEmissions
  unk := #[cost 0.0, cost 20.0, cost 20.0, cost 20.0, cost 20.0]

private def compiled? :
    Except Nlp.Sequence.NerTagger.CompileError Nlp.Sequence.NerTagger :=
  Nlp.Sequence.NerTagger.compile numeric words labels

private def compileAndLookup : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      tagger.nStates == 5 && tagger.wordNames == words && tagger.tagLabels == labels &&
        tagger.oov.toNat == words.size && tagger.encode "Alice" == 0 &&
        tagger.encode "alice" == tagger.oov && tagger.encode "unseen" == tagger.oov &&
        tagger.diagnosticSource == "in-memory NER tagger" &&
        (tagger.withDiagnosticSource "fixture").diagnosticSource == "fixture"

example : compileAndLookup = true := by native_decide

private def completeTagging : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      match tagger.tagForms words with
      | .error _ => false
      | .ok result =>
          let first := result.mentions[0]?
          let second := result.mentions[1]?
          result.start == 0 && result.stop == 4 && result.size == 4 &&
            result.tags ==
              #[parsed "B-PERSON", parsed "I-PERSON", parsed "O",
                parsed "B-ORGANIZATION"] &&
            result.labels == #["B-PERSON", "I-PERSON", "O", "B-ORGANIZATION"] &&
            result.classes == #["PERSON", "PERSON", "O", "ORGANIZATION"] &&
            result.mentions.size == 2 &&
            first.map (fun mention ↦
              (mention.start, mention.stop, mention.entity.name)) == some (0, 2, "PERSON") &&
            second.map (fun mention ↦
              (mention.start, mention.stop, mention.entity.name)) ==
                some (3, 4, "ORGANIZATION")

example : completeTagging = true := by native_decide

private def globalRangeCoordinates : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      match tagger.tagRange words 2 4 with
      | .error _ => false
      | .ok result =>
          result.start == 2 && result.stop == 4 && result.tags.size == 2 &&
            result.labels == #["O", "B-ORGANIZATION"] &&
            result.classes == #["O", "ORGANIZATION"] && result.mentions.size == 1 &&
            result.mentions[0]?.map (fun mention ↦
              (mention.start, mention.stop, mention.entity.name)) ==
                some (3, 4, "ORGANIZATION")

example : globalRangeCoordinates = true := by native_decide

private def encodeOnceParity : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      let encoded := tagger.encodeForms words
      match tagger.tagEncodedRange encoded 1 4, tagger.tagRange words 1 4 with
      | .ok left, .ok right =>
          left.start == right.start && left.stop == right.stop && left.tags == right.tags &&
            left.labels == right.labels && left.classes == right.classes
      | _, _ => false

example : encodeOnceParity = true := by native_decide

private def classOnlyParity : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      let encoded := tagger.encodeForms words
      match tagger.classesEncodedRange encoded 1 4, tagger.tagEncodedRange encoded 1 4,
          tagger.classesForms words with
      | .ok direct, .ok rich, .ok complete =>
          direct == rich.classes &&
            complete == #["PERSON", "PERSON", "O", "ORGANIZATION"]
      | _, _, _ => false

example : classOnlyParity = true := by native_decide

private def checkedStateProjection : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      let outOfBounds :=
        match tagger.classesFromStates #[99] 7 with
        | .error (.invalidState 7 99 5) => true
        | _ => false
      let orphan :=
        match tagger.classesFromStates #[2] 11 with
        | .error (.invalidPath (.orphanInside 11 "PERSON")) => true
        | _ => false
      let mismatch :=
        match tagger.classesFromStates #[1, 4] 20 with
        | .error (.invalidPath (.mismatchedInside 21 "PERSON" "ORGANIZATION")) => true
        | _ => false
      outOfBounds && orphan && mismatch

example : checkedStateProjection = true := by native_decide

private def normalizedRanges : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      let clipped := tagger.tagRange words 3 99
      let reversed := tagger.tagRange words 4 2
      match clipped, reversed with
      | .ok right, .ok empty =>
          right.start == 3 && right.stop == 4 && right.size == 1 &&
            empty.start == 2 && empty.stop == 2 && empty.tags.isEmpty &&
            empty.labels.isEmpty && empty.classes.isEmpty && empty.mentions.isEmpty
      | _, _ => false

example : normalizedRanges = true := by native_decide

private def unknownUsesCollisionFreeOov : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      tagger.decodeForms #["ALICE"] == #[0] &&
        match tagger.tagForms #["ALICE"] with
        | .ok result => result.labels == #["O"] && result.classes == #["O"]
        | .error _ => false

example : unknownUsesCollisionFreeOov = true := by native_decide

private def rejectsWordNames : Bool :=
  let empty :=
    match Nlp.Sequence.NerTagger.compile numeric #["Alice", "", "at", "Acme"] labels with
    | .error (.emptyWordName 1) => true
    | _ => false
  let duplicate :=
    match Nlp.Sequence.NerTagger.compile numeric #["Alice", "Smith", "Alice", "Acme"]
        labels with
    | .error (.duplicateWordName 0 2 "Alice") => true
    | _ => false
  empty && duplicate

example : rejectsWordNames = true := by native_decide

private def rejectsBadCanonicalLabel : Bool :=
  let malformed := #["O", "B-PERSON", "I-PERSON", "B-", "I-ORGANIZATION"]
  match Nlp.Sequence.NerTagger.compile numeric words malformed with
  | .error (.invalidTagLabel 3 "B-" (.emptyEntity "B-")) => true
  | _ => false

example : rejectsBadCanonicalLabel = true := by native_decide

private def rejectsBackgroundEntityCollision : Bool :=
  let compileFailure :=
    let collisionLabels := #["O", "B-O", "I-O", "B-PERSON", "I-PERSON"]
    match Nlp.Sequence.NerTagger.compile numeric words collisionLabels with
    | .error (.reservedEntityType 1 "B-O") => true
    | _ => false
  let trainingFailure :=
    match Nlp.Sequence.NerTagger.estimate #[#[("background", "B-O")]] with
    | .error (.reservedTrainingEntityType 0 0 "B-O") => true
    | _ => false
  compileFailure && trainingFailure

example : rejectsBackgroundEntityCollision = true := by native_decide

private def rejectsConstrainedInventories : Bool :=
  let duplicate :=
    match Nlp.Sequence.NerTagger.compile numeric words
        #["O", "B-PERSON", "B-PERSON", "B-ORGANIZATION", "I-ORGANIZATION"] with
    | .error (.constrained (.duplicateTag 1 2 "B-PERSON")) => true
    | _ => false
  let missingOutside :=
    match Nlp.Sequence.NerTagger.compile numeric words
        #["B-PERSON", "I-PERSON", "B-ORGANIZATION", "I-ORGANIZATION", "B-PLACE"] with
    | .error (.constrained .missingOutside) => true
    | _ => false
  let orphan :=
    match Nlp.Sequence.NerTagger.compile numeric words
        #["O", "I-GHOST", "B-PERSON", "I-PERSON", "B-ORGANIZATION"] with
    | .error (.constrained (.orphanInside 1 "GHOST")) => true
    | _ => false
  duplicate && missingOutside && orphan

example : rejectsConstrainedInventories = true := by native_decide

private def rejectsNumericFailure : Bool :=
  let malformed := { numeric with unk := #[] }
  match Nlp.Sequence.NerTagger.compile malformed words labels with
  | .error (.constrained (.invalidDimensions 5 5 25 0)) => true
  | _ => false

example : rejectsNumericFailure = true := by native_decide

private def rejectsOovEmission : Bool :=
  let key := Hmm.emissionKey 0 (UInt32.ofNat words.size)
  let malformed := { numeric with emit := numeric.emit.insert key (cost 0.0) }
  match Nlp.Sequence.NerTagger.compile malformed words labels with
  | .error (.emissionWordOutOfRange found 4 4) => found == key
  | _ => false

example : rejectsOovEmission = true := by native_decide

private def deterministicEmissionFailure : Bool :=
  let lower := Hmm.emissionKey 0 7
  let higher := Hmm.emissionKey 1 6
  let firstHigher := numeric.emit.insert higher (cost 0.0) |>.insert lower (cost 0.0)
  let firstLower := numeric.emit.insert lower (cost 0.0) |>.insert higher (cost 0.0)
  let reportsLower := fun emissions ↦
    match Nlp.Sequence.NerTagger.compile { numeric with emit := emissions } words labels with
    | .error (.emissionWordOutOfRange key 7 4) => key == lower
    | _ => false
  reportsLower firstHigher && reportsLower firstLower

example : deterministicEmissionFailure = true := by native_decide

private def training : Array (Array (String × String)) :=
  #[#[("Alice", "B-PERSON"), ("Smith", "I-PERSON"), ("left", "O")],
    #[("Acme", "B-ORGANIZATION"), ("hired", "O")]]

private def estimatesInFirstOccurrenceOrder : Bool :=
  match Nlp.Sequence.NerTagger.estimate training with
  | .error _ => false
  | .ok tagger =>
      tagger.wordNames == #["Alice", "Smith", "left", "Acme", "hired"] &&
        tagger.tagLabels == #["B-PERSON", "I-PERSON", "O", "B-ORGANIZATION"] &&
        tagger.nStates == 4 && tagger.oov.toNat == 5 &&
        match tagger.tagForms #["Alice", "unseen"] with
        | .ok result => result.tags.size == 2 && result.classes.size == 2
        | .error _ => false

example : estimatesInFirstOccurrenceOrder = true := by native_decide

private def trainingErrorsRetainCoordinates : Bool :=
  let emptyForm :=
    match Nlp.Sequence.NerTagger.estimate #[#[("", "O")]] with
    | .error (.emptyTrainingForm 0 0) => true
    | _ => false
  let invalidTag :=
    match Nlp.Sequence.NerTagger.estimate
        #[#[("ok", "O")], #[("bad", "PERSON")]] with
    | .error (.invalidTrainingTag 1 0 "PERSON" (.invalidLabel "PERSON")) => true
    | _ => false
  let illegalStart :=
    match Nlp.Sequence.NerTagger.estimate #[#[("Smith", "I-PERSON")]] with
    | .error (.illegalTrainingStart 0 0 "I-PERSON") => true
    | _ => false
  let illegalEdge :=
    match Nlp.Sequence.NerTagger.estimate
        #[#[("Alice", "B-PERSON"), ("Corp", "I-ORGANIZATION")]] with
    | .error (.illegalTrainingTransition 0 1 "B-PERSON" "I-ORGANIZATION") => true
    | _ => false
  emptyForm && invalidTag && illegalStart && illegalEdge

example : trainingErrorsRetainCoordinates = true := by native_decide

private def extractsMentions : Bool :=
  let tags :=
    #[parsed "B-PERSON", parsed "I-PERSON", parsed "O",
      parsed "B-ORGANIZATION", parsed "B-PERSON"]
  match Nlp.Sequence.NerTagger.extractMentions tags 10 with
  | .error _ => false
  | .ok mentions =>
      mentions.size == 3 &&
        mentions[0]?.map (fun mention ↦
          (mention.start, mention.stop, mention.entity.name)) == some (10, 12, "PERSON") &&
        mentions[1]?.map (fun mention ↦
          (mention.start, mention.stop, mention.entity.name)) ==
            some (13, 14, "ORGANIZATION") &&
        mentions[2]?.map (fun mention ↦
          (mention.start, mention.stop, mention.entity.name)) == some (14, 15, "PERSON")

example : extractsMentions = true := by native_decide

private def rejectsInvalidMentionPaths : Bool :=
  let orphan :=
    match Nlp.Sequence.NerTagger.extractMentions #[parsed "I-PERSON"] 7 with
    | .error (.orphanInside 7 "PERSON") => true
    | _ => false
  let mismatch :=
    match Nlp.Sequence.NerTagger.extractMentions
        #[parsed "B-PERSON", parsed "I-ORGANIZATION"] 4 with
    | .error (.mismatchedInside 5 "PERSON" "ORGANIZATION") => true
    | _ => false
  orphan && mismatch

example : rejectsInvalidMentionPaths = true := by native_decide

/-- Named range decoding exposes its normalized output-size law. -/
example (tagger : Nlp.Sequence.NerTagger) (forms : Array String) (start stop : Nat) :
    (tagger.decodeRange forms start stop).size =
      Nlp.Sequence.NerTagger.rangeLength forms start stop :=
  tagger.decodeRange_size forms start stop

/-- Successful complete taggings expose one typed tag and both labels per form. -/
example (tagger : Nlp.Sequence.NerTagger) (forms : Array String)
    (tagging : Nlp.Sequence.NerTagger.Tagging)
    (success : tagger.tagForms forms = .ok tagging) :
    tagging.tags.size = forms.size ∧ tagging.labels.size = forms.size ∧
      tagging.classes.size = forms.size := by
  have size := tagger.tagForms_size_of_ok forms tagging success
  simpa using And.intro (tagging.tags_size.trans size)
    (And.intro (tagging.labels_size.trans size) (tagging.classes_size.trans size))

/-- Mention nonemptiness is certified by the private-constructor result type. -/
example (mention : Nlp.Sequence.NerTagger.Mention) : mention.start < mention.stop :=
  mention.start_lt_stop

/-- Rich string projections remain theorem-level functions of typed BIO2 output. -/
example (tagging : Nlp.Sequence.NerTagger.Tagging) :
    tagging.labels = tagging.tags.map Tag.render ∧
      tagging.classes = tagging.tags.map Nlp.Sequence.NerTagger.entityClass := by
  exact And.intro tagging.labels_eq_map tagging.classes_eq_map

end NlpTests.Sequence.NerTagger
