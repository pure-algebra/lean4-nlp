import Nlp.Sequence.PosTagger

namespace NlpTests.Sequence.PosTagger

open Nlp Nlp.Sequence

private def cost (value : Float) : Cost := ⟨value⟩

private def emissions : Std.HashMap UInt64 Cost :=
  ({} : Std.HashMap UInt64 Cost)
    |>.insert (Hmm.emissionKey 0 0) (cost 0.0)
    |>.insert (Hmm.emissionKey 1 0) (cost 8.0)
    |>.insert (Hmm.emissionKey 0 1) (cost 8.0)
    |>.insert (Hmm.emissionKey 1 1) (cost 0.0)

private def numeric : Hmm where
  nTags := 2
  start := #[cost 0.0, cost 8.0]
  trans := #[cost 0.0, cost 0.0, cost 8.0, cost 0.0]
  emit := emissions
  unk := #[cost 10.0, cost 10.0]

private def compiled? : Except Nlp.Sequence.PosTagger.CompileError Nlp.Sequence.PosTagger :=
  Nlp.Sequence.PosTagger.compile numeric #["dogs", "run"] #["NOUN", "VERB"]

private def compileAndDecode : Bool :=
  match compiled? with
  | .error _ => false
  | .ok tagger =>
      tagger.wordNames == #["dogs", "run"] && tagger.tagNames == #["NOUN", "VERB"] &&
        tagger.oov.toNat == 2 && tagger.encode "dogs" == 0 && tagger.encode "run" == 1 &&
        tagger.encode "Dogs" == tagger.oov && tagger.encode "unknown" == tagger.oov &&
        tagger.decodeForms #["dogs", "run"] == #[0, 1] &&
        tagger.tagForms #["dogs", "run"] == #["NOUN", "VERB"]

#guard compileAndDecode

private def caseSensitiveNames : Bool :=
  match Nlp.Sequence.PosTagger.compile numeric #["dogs", "Dogs"] #["NOUN", "VERB"] with
  | .ok tagger => tagger.encode "dogs" == 0 && tagger.encode "Dogs" == 1
  | .error _ => false

#guard caseSensitiveNames

private def oneTagEstimate : Bool :=
  match Nlp.Sequence.PosTagger.estimate
      #[#[("dogs", "NOUN"), ("dogs", "NOUN")], #[("dog", "NOUN")]] with
  | .error _ => false
  | .ok tagger =>
      tagger.wordNames == #["dogs", "dog"] && tagger.tagNames == #["NOUN"] &&
        tagger.hmm.nTags == 1 && tagger.tagForms #["dogs", "unseen"] == #["NOUN", "NOUN"]

#guard oneTagEstimate

private def rejectsZeroTags : Bool :=
  match Nlp.Sequence.PosTagger.compile { numeric with nTags := 0 } #[] #[] with
  | .error .zeroTags => true
  | _ => false

#guard rejectsZeroTags

private def rejectsDimensions : Bool :=
  match Nlp.Sequence.PosTagger.compile { numeric with unk := #[] }
      #["dogs", "run"] #["NOUN", "VERB"] with
  | .error (.invalidDimensions 2 2 4 0) => true
  | _ => false

#guard rejectsDimensions

private def rejectsTagCount : Bool :=
  match Nlp.Sequence.PosTagger.compile numeric #["dogs", "run"] #["NOUN"] with
  | .error (.invalidTagCount 2 1) => true
  | _ => false

#guard rejectsTagCount

private def rejectsEmptyNames : Bool :=
  let wordFailure :=
    match Nlp.Sequence.PosTagger.compile numeric #["dogs", ""] #["NOUN", "VERB"] with
    | .error (.emptyWordName 1) => true
    | _ => false
  let tagFailure :=
    match Nlp.Sequence.PosTagger.compile numeric #["dogs", "run"] #["NOUN", ""] with
    | .error (.emptyTagName 1) => true
    | _ => false
  wordFailure && tagFailure

#guard rejectsEmptyNames

private def rejectsDuplicateNames : Bool :=
  let wordFailure :=
    match Nlp.Sequence.PosTagger.compile numeric #["dogs", "dogs"] #["NOUN", "VERB"] with
    | .error (.duplicateWordName 0 1 "dogs") => true
    | _ => false
  let tagFailure :=
    match Nlp.Sequence.PosTagger.compile numeric #["dogs", "run"] #["NOUN", "NOUN"] with
    | .error (.duplicateTagName 0 1 "NOUN") => true
    | _ => false
  wordFailure && tagFailure

#guard rejectsDuplicateNames

private def rejectsNoncanonicalDenseCosts : Bool :=
  let negativeZero := Float.ofBits 0x8000000000000000
  let nan := Float.ofBits 0x7ff8000000000001
  let startFailure :=
    match Nlp.Sequence.PosTagger.compile { numeric with start := #[cost negativeZero, cost 1.0] }
        #["dogs", "run"] #["NOUN", "VERB"] with
    | .error (.invalidStartCost 0 value bits) =>
        value.toBits == negativeZero.toBits && bits == negativeZero.toBits
    | _ => false
  let transitionFailure :=
    match Nlp.Sequence.PosTagger.compile
        { numeric with trans := #[cost 0.0, cost (-1.0), cost 0.0, cost 0.0] }
        #["dogs", "run"] #["NOUN", "VERB"] with
    | .error (.invalidTransitionCost 1 value bits) =>
        value.toBits == (-1.0 : Float).toBits && bits == value.toBits
    | _ => false
  let unknownFailure :=
    match Nlp.Sequence.PosTagger.compile { numeric with unk := #[cost nan, cost 1.0] }
        #["dogs", "run"] #["NOUN", "VERB"] with
    | .error (.invalidUnknownCost 0 value bits) => value.isNaN && bits == value.toBits
    | _ => false
  startFailure && transitionFailure && unknownFailure

#guard rejectsNoncanonicalDenseCosts

private def rejectsBadEmissions : Bool :=
  let badTag := ({} : Std.HashMap UInt64 Cost).insert (Hmm.emissionKey 2 0) (cost 1.0)
  let badWord := ({} : Std.HashMap UInt64 Cost).insert (Hmm.emissionKey 0 2) (cost 1.0)
  let badCost :=
    ({} : Std.HashMap UInt64 Cost).insert (Hmm.emissionKey 0 0) (cost (1.0 / 0.0))
  let tagFailure :=
    match Nlp.Sequence.PosTagger.compile { numeric with emit := badTag }
        #["dogs", "run"] #["NOUN", "VERB"] with
    | .error (.emissionTagOutOfRange _ 2 2) => true
    | _ => false
  let wordFailure :=
    match Nlp.Sequence.PosTagger.compile { numeric with emit := badWord }
        #["dogs", "run"] #["NOUN", "VERB"] with
    | .error (.emissionWordOutOfRange _ 2 2) => true
    | _ => false
  let costFailure :=
    match Nlp.Sequence.PosTagger.compile { numeric with emit := badCost }
        #["dogs", "run"] #["NOUN", "VERB"] with
    | .error (.invalidEmissionCost _ value bits) => !value.isFinite && bits == value.toBits
    | _ => false
  tagFailure && wordFailure && costFailure

#guard rejectsBadEmissions

private def deterministicEmissionFailure : Bool :=
  let badWordKey := Hmm.emissionKey 0 2
  let badTagKey := Hmm.emissionKey 2 0
  let firstWord := ({} : Std.HashMap UInt64 Cost)
    |>.insert badTagKey (cost 1.0)
    |>.insert badWordKey (cost 1.0)
  let firstTag := ({} : Std.HashMap UInt64 Cost)
    |>.insert badWordKey (cost 1.0)
    |>.insert badTagKey (cost 1.0)
  let reportsWord := fun emissions ↦
    match Nlp.Sequence.PosTagger.compile { numeric with emit := emissions }
        #["dogs", "run"] #["NOUN", "VERB"] with
    | .error (.emissionWordOutOfRange key 2 2) => key == badWordKey
    | _ => false
  reportsWord firstWord && reportsWord firstTag

#guard deterministicEmissionFailure

private def estimateRejectsEmptyNames : Bool :=
  let wordFailure :=
    match Nlp.Sequence.PosTagger.estimate #[#[("", "NOUN")]] with
    | .error (.emptyWordName 0) => true
    | _ => false
  let tagFailure :=
    match Nlp.Sequence.PosTagger.estimate #[#[("dog", "")]] with
    | .error (.emptyTagName 0) => true
    | _ => false
  wordFailure && tagFailure

#guard estimateRejectsEmptyNames

end NlpTests.Sequence.PosTagger
