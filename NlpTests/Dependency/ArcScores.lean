import Nlp.Dependency.ArcScores

/-! Regression tests for checked labeled dependency-arc compilation. -/

namespace NlpTests.Dependency.ArcScores

open Nlp Nlp.Dependency

private def labels : Array String := #["root", "dep", "obj"]

private def scorer (head dependent relation : Nat) : Float :=
  if head = 0 then
    if dependent = 2 then 0.5 else 2.0
  else if relation = 1 then
    Float.ofNat (head + dependent)
  else
    Float.ofNat (head + dependent) + 1.0

private def compiled : Except ArcScoreError ArcScores :=
  ArcScores.compileScorer 3 labels 0 scorer

private def selectedCoordinates : Bool :=
  match compiled with
  | .error _ => false
  | .ok scores =>
      scores.n == 3 && scores.relationNames == labels &&
        scores.choice? 0 2 == some ⟨0.5, 0⟩ &&
        scores.choice? 3 1 == some ⟨4.0, 1⟩ &&
        (scores.choice? 1 1).isNone &&
        (scores.choice? 4 1).isNone &&
        scores.relationName? 2 == some "obj"

#guard selectedCoordinates

private def relationTieUsesLowerOrdinal : Bool :=
  match ArcScores.compileScorer 2 labels 0 fun head _ relation =>
      if head = 0 then 0.0 else if relation = 0 then 99.0 else 1.0 with
  | .error _ => false
  | .ok scores => scores.choice? 1 2 == some ⟨1.0, 1⟩

#guard relationTieUsesLowerOrdinal

#guard
  ArcScores.scoreVisitCount 3 3 == 15 &&
    ArcScores.entryCount 3 == 12 && ArcScores.denseEntryCount 3 3 == 36

private def rejectsDuplicateNames : Bool :=
  match ArcScores.compileScorer 1 #["root", "dep", "dep"] 0 scorer with
  | .error (.duplicateRelationName 1 2 "dep") => true
  | _ => false

#guard rejectsDuplicateNames

private def rejectsNegativeZero : Bool :=
  let negativeZero := Float.ofBits 0x8000000000000000
  match ArcScores.compileScorer 1 #["root"] 0 fun _ _ _ => negativeZero with
  | .error (.invalidCost 0 1 0 _ bits) => bits == 0x8000000000000000
  | _ => false

#guard rejectsNegativeZero

private def acceptsForbiddenInfinity : Bool :=
  match ArcScores.compileScorer 1 #["root"] 0 fun _ _ _ => inf with
  | .ok scores => (scores.choice? 0 1).isNone
  | .error _ => false

#guard acceptsForbiddenInfinity

private def rejectsDenseDimension : Bool :=
  match ArcScores.compileDense 2 labels 0 #[0.0] with
  | .error (.denseDimension expected 1) => expected == 18
  | _ => false

#guard rejectsDenseDimension

private def exactArcBudget : Bool :=
  let exact : ArcScoreConfig := {
    maxTokens := 2
    maxRelations := 3
    maxArcEntries := 6
    maxScoreVisits := 6
  }
  let short := { exact with maxArcEntries := 5 }
  (ArcScores.compileScorerWith exact 2 labels 0 scorer).isOk &&
    match ArcScores.compileScorerWith short 2 labels 0 scorer with
    | .error (.arcEntryBudget 6 5) => true
    | _ => false

#guard exactArcBudget

end NlpTests.Dependency.ArcScores
