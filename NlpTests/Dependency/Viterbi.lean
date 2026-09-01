import Nlp.Dependency.Viterbi

/-! Exact labeled and single-root regression tests for projective Viterbi inference. -/

namespace NlpTests.Dependency.Viterbi

open Nlp Nlp.Dependency

private def labels : Array String := #["root", "dep", "obj"]

private def middleRootScore (head dependent relation : Nat) : Float :=
  if head = 0 then
    if dependent = 2 then 1.0 else 20.0
  else if relation = 1 then
    if (head = 2 && dependent = 1) || (head = 2 && dependent = 3) then 1.0 else 10.0
  else
    5.0

private def middleRoot : Bool :=
  match ArcScores.compileScorer 3 labels 0 middleRootScore with
  | .error _ => false
  | .ok arcs =>
      match Eisner.parse? arcs, Eisner.parseNamed? arcs with
      | some result, some named =>
          result.heads == #[2, 0, 2] && result.relations == #[1, 0, 1] &&
            result.cost.toBits == (3.0 : Float).toBits &&
            named.heads == result.heads && named.relations == #["dep", "root", "dep"]
      | _, _ => false

#guard middleRoot

private def singleton : Bool :=
  match ArcScores.compileScorer 1 #["root"] 0 fun _ _ _ => 0.25 with
  | .error _ => false
  | .ok arcs =>
      match Eisner.parse? arcs with
      | some result =>
          result.heads == #[0] && result.relations == #[0] &&
            result.cost.toBits == (0.25 : Float).toBits
      | none => false

#guard singleton

private def exactlyOneRootOnTies : Bool :=
  match ArcScores.compileScorer 4 #["root", "dep"] 0 fun head _ _ =>
      if head = 0 then 0.0 else 1.0 with
  | .error _ => false
  | .ok arcs =>
      match Eisner.parse? arcs with
      | some result =>
          (result.heads.filter (· == 0)).size == 1 && result.heads[0]? == some 0
      | none => false

#guard exactlyOneRootOnTies

private def relationTieKeepsSourceOrdinal : Bool :=
  match ArcScores.compileScorer 2 labels 0 fun head _ relation =>
      if head = 0 then 0.0 else if relation = 0 then 100.0 else 1.0 with
  | .error _ => false
  | .ok arcs =>
      match Eisner.parse? arcs with
      | some result => result.relations == #[0, 1] && result.heads == #[0, 1]
      | none => false

#guard relationTieKeepsSourceOrdinal

private def forbiddenArcsHaveNoAnalysis : Bool :=
  match ArcScores.compileScorer 2 #["root", "dep"] 0 fun _ _ _ => inf with
  | .error _ => false
  | .ok arcs => (Eisner.parse? arcs).isNone

#guard forbiddenArcsHaveNoAnalysis

private def emptyHasNoAnalysis : Bool :=
  match ArcScores.compileScorer 0 #["root", "dep"] 0 fun _ _ _ => 0.0 with
  | .error _ => false
  | .ok arcs =>
      let chart := Eisner.viterbi arcs
      chart.score.size == 0 && (Eisner.extract? arcs chart).isNone

#guard emptyHasNoAnalysis

private def deterministic : Bool :=
  match ArcScores.compileScorer 5 #["root", "dep"] 0 fun head dependent _ =>
      Float.ofNat ((head * 7 + dependent * 11) % 5) with
  | .error _ => false
  | .ok arcs =>
      match Eisner.parse? arcs, Eisner.parse? arcs with
      | some first, some second =>
          first.heads == second.heads && first.relations == second.relations &&
            first.cost.toBits == second.cost.toBits
      | none, none => true
      | _, _ => false

#guard deterministic

private def genericValueParity (n seed : Nat) : Bool :=
  match ArcScores.compileScorer n #["root", "dep", "obj"] 0
      (fun head dependent relation =>
        Float.ofNat ((head * 17 + dependent * 11 + relation * 5 + seed) % 13) / 4.0) with
  | .error _ => false
  | .ok arcs =>
      let generic := Eisner.inside arcs.toArcWeights
      let specialized := Eisner.viterbi arcs
      generic.toFloat.toBits == specialized.rootCost.toBits

#guard genericValueParity 1 0
#guard genericValueParity 2 1
#guard genericValueParity 3 2
#guard genericValueParity 4 3
#guard genericValueParity 5 4

/-- Successful specialized extraction carries kernel-checked tree and projectivity proofs. -/
example (arcs : ArcScores) (result : Eisner.Result)
    (_found : Eisner.parse? arcs = some result) :
    SentenceTreeWF result.heads ∧ Projective result.heads :=
  ⟨result.wellFormed, result.projective⟩

end NlpTests.Dependency.Viterbi
