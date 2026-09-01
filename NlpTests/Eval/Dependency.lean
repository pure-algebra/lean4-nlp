import Nlp.Eval.Dependency

/-! # Dependency attachment evaluation tests -/

namespace NlpTests.Eval.Dependency

open Nlp.Eval.Dependency

/-- A four-token checked gold fixture including one punctuation dependent. -/
private def gold : GoldSentence String where
  heads := #[2, 0, 2, 2]
  relations := #["nsubj", "root", "obj", "punct"]
  pos := #["NOUN", "VERB", "NOUN", "PUNCT"]

/-- Heads all match while two labels differ. -/
private def labelErrors : PredictedSentence String where
  heads := #[2, 0, 2, 2]
  relations := #["obj", "root", "obj", "dep"]

/-- One content-word head differs while its displayed relation matches. -/
private def headError : PredictedSentence String where
  heads := #[2, 0, 1, 2]
  relations := gold.relations

/-- Exact heads contribute to UAS even when their relation labels differ. -/
example : (scoreSentence gold labelErrors).toOption =
    some { total := 4, uasCorrect := 4, lasCorrect := 2 } := by
  native_decide

/-- A wrong head is wrong for both UAS and LAS. -/
example : (scoreSentence gold headError).toOption =
    some { total := 4, uasCorrect := 3, lasCorrect := 3 } := by
  native_decide

/-- Caller-defined POS punctuation exclusion changes only the retained denominator and counts. -/
example :
    (scoreSentenceWith (.excludeByPos fun pos ↦ pos == "PUNCT") gold labelErrors).toOption =
      some { total := 3, uasCorrect := 3, lasCorrect := 2 } := by
  native_decide

/-- The token attached to artificial root is an ordinary scored dependent. -/
example :
    (scoreSentence
      { heads := #[0], relations := #["root"], pos := #["VERB"] }
      { heads := #[0], relations := #["root"] }).toOption =
      some { total := 1, uasCorrect := 1, lasCorrect := 1 } := by
  native_decide

/-- Excluding every dependent uses the shared zero-denominator convention. -/
private def zeroDenominator : Bool :=
  match scoreSentenceWith (.excludeByPos fun _ ↦ true) gold labelErrors with
  | .ok counts =>
    counts == 0 && counts.uas.toBits == (0.0 : Float).toBits &&
      counts.las.toBits == (0.0 : Float).toBits
  | .error _ => false

#guard zeroDenominator

/-- Gold relation alignment failures retain their validation side and exact dimensions. -/
private def malformedGoldRelations : Bool :=
  let malformed : GoldSentence String := {
    heads := #[2, 0]
    relations := #["dep"]
    pos := #["NOUN", "VERB"]
  }
  match scoreSentence malformed { heads := #[2, 0], relations := #["dep", "root"] } with
  | .error (.tree .gold (.relationCount 2 1)) => true
  | _ => false

#guard malformedGoldRelations

/-- Predicted tree failures remain distinct from dimension failures. -/
private def malformedPredictedTree : Bool :=
  let predicted : PredictedSentence String := {
    heads := #[2, 1]
    relations := #["dep", "dep"]
  }
  match scoreSentence
      { heads := #[2, 0], relations := #["dep", "root"], pos := #["NOUN", "VERB"] }
      predicted with
  | .error (.tree .predicted .noRoot) => true
  | _ => false

#guard malformedPredictedTree

/-- Checked trees of different lengths produce an explicit token-count error. -/
private def tokenCountMismatch : Bool :=
  match scoreSentence
      { heads := #[2, 0], relations := #["dep", "root"], pos := #["NOUN", "VERB"] }
      { heads := #[0], relations := #["root"] } with
  | .error (.tokenCountMismatch 2 1) => true
  | _ => false

#guard tokenCountMismatch

/-- POS dimensions are checked after both dependency trees. -/
private def posCountMismatch : Bool :=
  match scoreSentence
      { heads := #[2, 0], relations := #["dep", "root"], pos := #["NOUN"] }
      { heads := #[2, 0], relations := #["dep", "root"] } with
  | .error (.posCountMismatch 2 1) => true
  | _ => false

#guard posCountMismatch

/-- Corpus aggregation is exactly componentwise addition of sentence counts. -/
example : (scoreCorpus #[gold, gold] #[labelErrors, headError]).toOption =
    some { total := 8, uasCorrect := 7, lasCorrect := 5 } := by
  native_decide

/-- Empty aligned corpora produce the neutral count. -/
example : (scoreCorpus (#[] : Array (GoldSentence String)) #[]).toOption = some 0 := by
  native_decide

/-- Corpus alignment failures retain both sentence counts. -/
private def sentenceCountMismatch : Bool :=
  match scoreCorpus #[gold] (#[] : Array (PredictedSentence String)) with
  | .error (.sentenceCountMismatch 1 0) => true
  | _ => false

#guard sentenceCountMismatch

end NlpTests.Eval.Dependency
