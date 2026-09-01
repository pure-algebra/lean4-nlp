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

/-- Test-only recurrence retaining the public triangular index at every access. -/
private structure SlowChart where
  score : FloatArray
  split : Array UInt32
  root : UInt32
  rootCost : Float

/-- Reference implementation for exact optimized-chart regression checks. -/
private def slowViterbi (arcs : ArcScores) : SlowChart := Id.run do
  let n := arcs.n
  let entries := Eisner.chartEntryCount n
  let mut score := FloatArray.replicate entries inf
  let mut split := Array.replicate entries 0
  for token in [0:n] do
    score := score.set! (Eisner.itemIndex n token token .completeLeft) 0.0
    score := score.set! (Eisner.itemIndex n token token .completeRight) 0.0
  for width in [2:n + 1] do
    for i in [0:n + 1 - width] do
      let j := i + width - 1
      let mut common := inf
      let mut incompleteSplit := i
      for middle in [i:j] do
        let candidate :=
          score.getD (Eisner.itemIndex n i middle .completeRight) inf +
            score.getD (Eisner.itemIndex n (middle + 1) j .completeLeft) inf
        if candidate < common then
          common := candidate
          incompleteSplit := middle
      let leftIncomplete := Eisner.itemIndex n i j .incompleteLeft
      let rightIncomplete := Eisner.itemIndex n i j .incompleteRight
      score := score.set! leftIncomplete (common + arcs.costAt (j + 1) (i + 1))
      score := score.set! rightIncomplete (common + arcs.costAt (i + 1) (j + 1))
      split := split.set! leftIncomplete (UInt32.ofNat incompleteSplit)
      split := split.set! rightIncomplete (UInt32.ofNat incompleteSplit)
      let mut completeLeft := inf
      let mut leftSplit := i
      for middle in [i:j] do
        let candidate :=
          score.getD (Eisner.itemIndex n i middle .completeLeft) inf +
            score.getD (Eisner.itemIndex n middle j .incompleteLeft) inf
        if candidate < completeLeft then
          completeLeft := candidate
          leftSplit := middle
      let leftComplete := Eisner.itemIndex n i j .completeLeft
      score := score.set! leftComplete completeLeft
      split := split.set! leftComplete (UInt32.ofNat leftSplit)
      let mut completeRight := inf
      let mut rightSplit := i + 1
      for middle in [i + 1:j + 1] do
        let candidate :=
          score.getD (Eisner.itemIndex n i middle .incompleteRight) inf +
            score.getD (Eisner.itemIndex n middle j .completeRight) inf
        if candidate < completeRight then
          completeRight := candidate
          rightSplit := middle
      let rightComplete := Eisner.itemIndex n i j .completeRight
      score := score.set! rightComplete completeRight
      split := split.set! rightComplete (UInt32.ofNat rightSplit)
  let mut root := 0
  let mut rootCost := inf
  for candidateRoot in [0:n] do
    let candidate :=
      (score.getD (Eisner.itemIndex n 0 candidateRoot .completeLeft) inf +
        score.getD (Eisner.itemIndex n candidateRoot (n - 1) .completeRight) inf) +
        arcs.costAt 0 (candidateRoot + 1)
    if candidate < rootCost then
      root := candidateRoot
      rootCost := candidate
  return ⟨score, split, UInt32.ofNat root, rootCost⟩

/-- Compare unboxed chart values by exact IEEE-754 representation. -/
private def sameScoreBits (left right : FloatArray) : Bool := Id.run do
  unless left.size == right.size do
    return false
  for index in [0:left.size] do
    unless (left.getD index inf).toBits == (right.getD index inf).toBits do
      return false
  return true

/-- Optimized width-band indices preserve every reference value and backpointer. -/
private def exactChartParity (n seed : Nat) : Bool :=
  match ArcScores.compileScorer n labels 0 fun head dependent relation =>
      Float.ofNat ((head * 17 + dependent * 11 + relation * 5 + seed) % 13) / 4.0 with
  | .error _ => false
  | .ok arcs =>
      let reference := slowViterbi arcs
      let optimized := Eisner.viterbi arcs
      sameScoreBits reference.score optimized.score && reference.split == optimized.split &&
        reference.root == optimized.root &&
          reference.rootCost.toBits == optimized.rootCost.toBits

#guard (List.range 9).all fun n ↦ exactChartParity n (n * 7 + 3)

-- Forbidden arcs and exact ties retain the reference chart bit for bit.
#guard
  match ArcScores.compileScorer 6 #["root", "dep"] 0 fun head _ _ =>
      if head = 0 then 0.0 else inf with
  | .error _ => false
  | .ok arcs =>
      let reference := slowViterbi arcs
      let optimized := Eisner.viterbi arcs
      sameScoreBits reference.score optimized.score && reference.split == optimized.split &&
        reference.root == optimized.root &&
          reference.rootCost.toBits == optimized.rootCost.toBits

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
