import Nlp.Eval.Evalb

namespace NlpTests.Eval.Evalb

open Nlp.Eval.Evalb

private def sampleParams : String :=
  include_str ".." / "Fixtures" / "Evalb" / "sample.prm"

private def sampleGold : String :=
  include_str ".." / "Fixtures" / "Evalb" / "sample.gld"

private def sampleTest : String :=
  include_str ".." / "Fixtures" / "Evalb" / "sample.tst"

private def sampleScore : Except Error CorpusScore := do
  let params ← parseParams sampleParams
  scorePtbText params sampleGold sampleTest

private def expectedAll : Summary where
  sentences := 24
  errors := 5
  skipped := 2
  valid := 17
  matched := 86
  goldBrackets := 98
  testBrackets := 95
  complete := 9
  crossing := 1
  noCrossing := 16
  atMostTwoCrossing := 17
  words := 108
  correctTags := 106

private def expectedCutoff : Summary where
  sentences := 23
  errors := 5
  skipped := 2
  valid := 16
  matched := 52
  goldBrackets := 64
  testBrackets := 61
  complete := 8
  crossing := 1
  noCrossing := 15
  atMostTwoCrossing := 16
  words := 64
  correctTags := 62

/-- Exact regression against EVALB's public-domain sample corpus. -/
private def sampleMatches : Bool :=
  match sampleScore with
  | .ok score => score.all == expectedAll && score.cutoff == expectedCutoff
  | .error _ => false

#guard sampleMatches

example : (Params.collins.compile).isOk := by native_decide

private structure FixtureRow where
  status : Nat := 0
  len : Nat := 0
  matched : Nat := 0
  goldBrackets : Nat := 0
  testBrackets : Nat := 0
  crossing : Nat := 0
  words : Nat := 0
  correctTags : Nat := 0
deriving BEq, Inhabited

private def fixtureRow : SentenceResult → FixtureRow
  | .valid score => {
      status := 0
      len := score.len
      matched := score.matched
      goldBrackets := score.goldBrackets
      testBrackets := score.testBrackets
      crossing := score.crossing
      words := score.words
      correctTags := score.correctTags
    }
  | .error len words _ => { status := 1, len, words }
  | .skipped len words => { status := 2, len, words }

private def expectedRows : Array FixtureRow :=
  #[⟨0, 4, 4, 4, 4, 0, 4, 4⟩, ⟨0, 4, 3, 4, 4, 0, 4, 4⟩,
    ⟨0, 4, 4, 4, 4, 0, 4, 3⟩, ⟨0, 4, 3, 4, 4, 0, 4, 3⟩,
    ⟨0, 4, 3, 4, 4, 0, 4, 4⟩, ⟨0, 4, 2, 4, 3, 1, 4, 4⟩,
    ⟨0, 4, 1, 4, 1, 0, 4, 4⟩, ⟨0, 4, 0, 4, 0, 0, 4, 4⟩,
    ⟨0, 4, 4, 4, 5, 0, 4, 4⟩, ⟨0, 4, 4, 4, 8, 0, 4, 4⟩,
    ⟨2, 4, 0, 0, 0, 0, 4, 0⟩, ⟨1, 4, 0, 0, 0, 0, 4, 0⟩,
    ⟨1, 4, 0, 0, 0, 0, 4, 0⟩, ⟨2, 4, 0, 0, 0, 0, 4, 0⟩,
    ⟨0, 4, 4, 4, 4, 0, 4, 4⟩, ⟨1, 4, 0, 0, 0, 0, 4, 0⟩,
    ⟨1, 4, 0, 0, 0, 0, 4, 0⟩, ⟨0, 4, 4, 4, 4, 0, 4, 4⟩,
    ⟨0, 4, 4, 4, 4, 0, 4, 4⟩, ⟨1, 4, 0, 0, 0, 0, 4, 0⟩,
    ⟨0, 4, 4, 4, 4, 0, 4, 4⟩, ⟨0, 44, 34, 34, 34, 0, 44, 44⟩,
    ⟨0, 4, 4, 4, 4, 0, 4, 4⟩, ⟨0, 5, 4, 4, 4, 0, 4, 4⟩]

private def fixtureRowsMatch : Bool :=
  match sampleScore with
  | .ok score => score.results.map fixtureRow == expectedRows
  | .error _ => false

#guard fixtureRowsMatch

private def oneMatched (params : Params) (gold test : String) : Option Nat := do
  let score ← (scorePtbText params gold test).toOption
  match score.results[0]? with
  | some (SentenceResult.valid sentence) => some sentence.matched
  | _ => none

private def overlapping : Params :=
  { Params.empty with eqLabel := #[("A", "B"), ("B", "C")] }

#guard oneMatched overlapping "(A (P x))" "(B (P x))" == some 1
#guard oneMatched overlapping "(A (P x))" "(C (P x))" == some 0

private def malformedEqRejected : Bool :=
  match parseParams "EQ_LABEL A B C" with
  | .error (.malformedParameter 1 _) => true
  | _ => false

#guard malformedEqRejected

private def unsupportedWrapperRejected : Bool :=
  match scorePtbText Params.empty "((S (P x)))" "((S (P x)))" with
  | .error (.unsupportedTextShape 1 1 _) => true
  | _ => false

#guard unsupportedWrapperRejected

private def unsupportedEmptyNodeRejected : Bool :=
  match scorePtbText Params.empty "(S (X) (P x))" "(S (X) (P x))" with
  | .error (.unsupportedTextShape 1 _ _) => true
  | _ => false

#guard unsupportedEmptyNodeRejected

private def quoteParams : Params :=
  { Params.empty with deleteLabel := #["''"], quoteLabel := #["''", "NN"] }

private def quoteRepairWorks : Bool :=
  match scorePtbText quoteParams "(S ('' \"))" "(S (NN \"))" with
  | .ok score =>
      match score.results[0]? with
      | some (SentenceResult.valid sentence) =>
          sentence.words == 1 && sentence.matched == 1 && sentence.correctTags == 0
      | _ => false
  | .error _ => false

#guard quoteRepairWorks

private def emptyCorpusWorks : Bool :=
  match scorePtbText Params.empty "" "" with
  | .ok score => score.results.isEmpty && score.all.sentences == 0
  | .error _ => false

#guard emptyCorpusWorks

end NlpTests.Eval.Evalb
