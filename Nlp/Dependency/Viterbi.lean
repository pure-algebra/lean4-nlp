import Nlp.Core.Data.ChartLayout
import Nlp.Core.Data.Dependency
import Nlp.Dependency.ArcScores
import Nlp.Dependency.Eisner

/-!
# Labeled one-best projective dependency parsing

This is the unboxed min-cost specialization of Eisner's four-item recurrence. Label selection is
already compiled by `ArcScores`, so inference costs `O(n^3)` time and `O(n^2)` storage regardless
of the number of dependency relations.

The chart ranges only over real tokens. Exactly one artificial-root arc is selected in a final
root recurrence that joins the complete left and right halves headed by the chosen token. This
avoids the multiple-root analyses admitted by an unrestricted dummy-root chart.

Ties are deterministic: `ArcScores` first preserves the lower relation ordinal, every chart item
preserves the lower split, and the final recurrence preserves the lower root token. Extraction is
total and rechecks every stored split and every exact IEEE-754 recurrence before returning a tree.
-/

namespace Nlp.Dependency.Eisner

/-- Four scores and four split ordinals for every nonempty inclusive token interval. -/
structure VitChart where
  private mk ::
  /-- Number of real tokens. -/
  n : Nat
  /-- Width-major, unboxed item scores. -/
  score : FloatArray
  /-- Parallel split fenceposts in 0-based real-token coordinates. -/
  split : Array UInt32
  /-- Selected 0-based real-token root; meaningful only when `rootCost` is finite. -/
  root : UInt32
  /-- Cost of the final single-root analysis, or positive infinity when none exists. -/
  rootCost : Float

/-- Exact labeled dependency output in CoNLL-U head coordinates. -/
structure Result where
  private mk ::
  /-- `heads[i]` is the 1-based head of dependent `i + 1`; zero is artificial root. -/
  heads : Array Nat
  /-- Exact relation ordinals selected from `ArcScores.relationNames`. -/
  relations : Array UInt32
  /-- Operational Float cost selected by the chart. -/
  cost : Float
  /-- Heads and exact relation ordinals are positionally aligned. -/
  aligned : relations.size = heads.size
  /-- The extracted heads form one general dependency tree. -/
  wellFormed : SentenceTreeWF heads
  /-- The extracted single-root tree contains no crossing arcs. -/
  projective : Projective heads

/-- Named view of one exact dependency result. -/
structure NamedResult where
  /-- CoNLL-U-coordinate dependency heads. -/
  heads : Array Nat
  /-- Caller-supplied relation names aligned with `heads`. -/
  relations : Array String
  /-- Operational Float cost selected by the chart. -/
  cost : Float
  deriving Repr, DecidableEq, Inhabited

/-- Number of scalar score or split entries in an `n`-token chart. -/
@[inline] def chartEntryCount (n : Nat) : Nat :=
  entryCount n

/-- Flat item address, mapping inclusive `[i, j]` to fencepost span `[i, j + 1)`. -/
@[inline] def itemIndex (n i j : Nat) (item : Item) : Nat :=
  flatIndex n i j item

/-- Conservatively read a chart item, returning infinity for malformed storage. -/
@[inline] def VitChart.getCost (chart : VitChart) (i j : Nat) (item : Item) : Float :=
  if i ≤ j && j < chart.n then
    chart.score.getD (itemIndex chart.n i j item) inf
  else
    inf

/-- Conservatively read one split from a chart. -/
@[inline] def VitChart.getSplit (chart : VitChart) (i j : Nat) (item : Item) : Nat :=
  chart.split.getD (itemIndex chart.n i j item) 0 |>.toNat

/-- Compute an exact-tie, lower-split argmin over a half-open split range. -/
private def bestSplit (first stop : Nat) (candidate : Nat → Float) : Float × Nat := Id.run do
  let mut best := inf
  let mut split := first
  for current in [first:stop] do
    let value := candidate current
    if value < best then
      best := value
      split := current
  return (best, split)

/--
Run single-root labeled Eisner inference over precompiled arc scores.

Every source cost is nonnegative or positive infinity, so recurrence addition cannot introduce a
NaN. Finite source values may still overflow to infinity; in that case the affected analysis is
treated as unavailable rather than being returned with unverifiable provenance.
-/
def viterbi (arcs : ArcScores) : VitChart := Id.run do
  let n := arcs.n
  let entries := chartEntryCount n
  let mut score := FloatArray.replicate entries inf
  let mut split := Array.replicate entries 0
  for token in [0:n] do
    score := score.set! (itemIndex n token token .completeLeft) 0.0
    score := score.set! (itemIndex n token token .completeRight) 0.0
  for width in [2:n + 1] do
    for i in [0:n + 1 - width] do
      let j := i + width - 1
      let (common, incompleteSplit) := bestSplit i j fun middle =>
        score.getD (itemIndex n i middle .completeRight) inf +
          score.getD (itemIndex n (middle + 1) j .completeLeft) inf
      let leftCost := common + arcs.costAt (j + 1) (i + 1)
      let rightCost := common + arcs.costAt (i + 1) (j + 1)
      let leftIncomplete := itemIndex n i j .incompleteLeft
      let rightIncomplete := itemIndex n i j .incompleteRight
      score := score.set! leftIncomplete leftCost
      score := score.set! rightIncomplete rightCost
      split := split.set! leftIncomplete (UInt32.ofNat incompleteSplit)
      split := split.set! rightIncomplete (UInt32.ofNat incompleteSplit)
      let (completeLeft, leftSplit) := bestSplit i j fun middle =>
        score.getD (itemIndex n i middle .completeLeft) inf +
          score.getD (itemIndex n middle j .incompleteLeft) inf
      let leftComplete := itemIndex n i j .completeLeft
      score := score.set! leftComplete completeLeft
      split := split.set! leftComplete (UInt32.ofNat leftSplit)
      let (completeRight, rightSplit) := bestSplit (i + 1) (j + 1) fun middle =>
        score.getD (itemIndex n i middle .incompleteRight) inf +
          score.getD (itemIndex n middle j .completeRight) inf
      let rightComplete := itemIndex n i j .completeRight
      score := score.set! rightComplete completeRight
      split := split.set! rightComplete (UInt32.ofNat rightSplit)
  let mut root := 0
  let mut rootCost := inf
  for candidateRoot in [0:n] do
    let candidate :=
      (score.getD (itemIndex n 0 candidateRoot .completeLeft) inf +
        score.getD (itemIndex n candidateRoot (n - 1) .completeRight) inf) +
        arcs.costAt 0 (candidateRoot + 1)
    if candidate < rootCost then
      root := candidateRoot
      rootCost := candidate
  return .mk n score split (UInt32.ofNat root) rootCost

/-- Mutable-looking extraction state threaded purely through the total backtrace. -/
private structure ExtractState where
  heads : Array Nat
  relations : Array UInt32
  assigned : Array Bool

/-- Exact Float equality used for recurrence validation, including signed zero. -/
@[inline] private def sameBits (left right : Float) : Bool :=
  left.toBits == right.toBits

/-- Assign one dependent exactly once during a checked backtrace. -/
private def assign (state : ExtractState) (dependentIndex head : Nat)
    (relation : UInt32) : Option ExtractState := do
  let already ← state.assigned[dependentIndex]?
  if already then
    none
  else
    some {
      heads := state.heads.set! dependentIndex head
      relations := state.relations.set! dependentIndex relation
      assigned := state.assigned.set! dependentIndex true
    }

/-- Recursively validate one item and materialize its arcs. -/
private def extractItem (arcs : ArcScores) (chart : VitChart) :
    Nat → Item → Nat → Nat → ExtractState → Option ExtractState
  | 0, _, _, _, _ => none
  | fuel + 1, item, i, j, state => do
      if !(i ≤ j && j < chart.n) then none else pure ()
      let stored := chart.getCost i j item
      if i = j then
        match item with
        | .completeLeft | .completeRight =>
            if sameBits stored 0.0 then some state else none
        | .incompleteLeft | .incompleteRight => none
      else
        let middle := chart.getSplit i j item
        match item with
        | .incompleteLeft =>
            if !(i ≤ middle && middle < j) then none else pure ()
            let choice ← arcs.choice? (j + 1) (i + 1)
            let left := chart.getCost i middle .completeRight
            let right := chart.getCost (middle + 1) j .completeLeft
            if !sameBits stored ((left + right) + choice.cost) then none else pure ()
            let next ← assign state i (j + 1) choice.relation
            let afterLeft ←
              extractItem arcs chart fuel .completeRight i middle next
            extractItem arcs chart fuel .completeLeft (middle + 1) j afterLeft
        | .incompleteRight =>
            if !(i ≤ middle && middle < j) then none else pure ()
            let choice ← arcs.choice? (i + 1) (j + 1)
            let left := chart.getCost i middle .completeRight
            let right := chart.getCost (middle + 1) j .completeLeft
            if !sameBits stored ((left + right) + choice.cost) then none else pure ()
            let next ← assign state j (i + 1) choice.relation
            let afterLeft ←
              extractItem arcs chart fuel .completeRight i middle next
            extractItem arcs chart fuel .completeLeft (middle + 1) j afterLeft
        | .completeLeft =>
            if !(i ≤ middle && middle < j) then none else pure ()
            let left := chart.getCost i middle .completeLeft
            let right := chart.getCost middle j .incompleteLeft
            if !sameBits stored (left + right) then none else pure ()
            let afterLeft ← extractItem arcs chart fuel .completeLeft i middle state
            extractItem arcs chart fuel .incompleteLeft middle j afterLeft
        | .completeRight =>
            if !(i < middle && middle ≤ j) then none else pure ()
            let left := chart.getCost i middle .incompleteRight
            let right := chart.getCost middle j .completeRight
            if !sameBits stored (left + right) then none else pure ()
            let afterLeft ← extractItem arcs chart fuel .incompleteRight i middle state
            extractItem arcs chart fuel .completeRight middle j afterLeft

/--
Extract and revalidate the exact analysis selected by a Viterbi chart.

Malformed dimensions, roots, splits, arc choices, recurrence values, duplicate assignments, or
incomplete assignments return `none`.
-/
def extract? (arcs : ArcScores) (chart : VitChart) : Option Result := do
  if chart.n != arcs.n || chart.n = 0 then none else pure ()
  let entries := chartEntryCount chart.n
  if chart.score.size != entries || chart.split.size != entries then none else pure ()
  if !chart.rootCost.isFinite then none else pure ()
  let root := chart.root.toNat
  if !(root < chart.n) then none else pure ()
  let rootChoice ← arcs.choice? 0 (root + 1)
  let left := chart.getCost 0 root .completeLeft
  let right := chart.getCost root (chart.n - 1) .completeRight
  if !sameBits chart.rootCost ((left + right) + rootChoice.cost) then none else pure ()
  let initial : ExtractState := {
    heads := Array.replicate chart.n 0
    relations := Array.replicate chart.n arcs.rootRelation
    assigned := (Array.replicate chart.n false).set! root true
  }
  let withRoot : ExtractState := {
    initial with relations := initial.relations.set! root rootChoice.relation
  }
  let fuel := chart.n * 2 + 2
  let afterLeft ← extractItem arcs chart fuel .completeLeft 0 root withRoot
  let complete ←
    extractItem arcs chart fuel .completeRight root (chart.n - 1) afterLeft
  if complete.assigned.all (· == true) then
    match _checkedTree : Tree.ofArrays complete.heads complete.relations with
    | .error _ => none
    | .ok tree =>
      match checkedProjective : checkProjective tree.heads with
      | .error _ => none
      | .ok () =>
        some (.mk tree.heads tree.relations chart.rootCost tree.aligned tree.wellFormed
          ((checkProjective_eq_ok_iff tree.heads).1 checkedProjective))
  else
    none

/-- Run inference and extract its exact labeled single-root analysis. -/
@[inline] def parse? (arcs : ArcScores) : Option Result :=
  extract? arcs (viterbi arcs)

/-- Resolve every exact relation ordinal, rejecting any corrupted or mismatched result. -/
def Result.resolve? (arcs : ArcScores) (result : Result) : Option NamedResult := do
  if result.heads.size != arcs.n || result.relations.size != arcs.n then none else pure ()
  let mut names := Array.emptyWithCapacity arcs.n
  for relation in result.relations do
    let name ← arcs.relationName? relation
    names := names.push name
  return ⟨result.heads, names, result.cost⟩

/-- Parse and resolve exact relation names in one pure operation. -/
def parseNamed? (arcs : ArcScores) : Option NamedResult := do
  let result ← parse? arcs
  result.resolve? arcs

end Nlp.Dependency.Eisner
