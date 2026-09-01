import Nlp.Core.Algebra.Laws
import Nlp.Core.Data.ChartLayout

/-!
# Algebraic projective dependency inference

This module implements the first-order Eisner inside recurrence over a caller-supplied semiring.
There are `n` real tokens, indexed `0, ..., n - 1` inside the kernel. `rootWeight dependent`
scores the one artificial-root arc, while `tokenWeight head dependent` scores an arc between two
distinct real tokens. Label alternatives must already have been collapsed with semiring addition.

The final recurrence chooses exactly one real token as the root. It does not insert the artificial
root into the four-item chart, which prevents the ordinary complete-item recurrence from adding
more than one artificial-root child. External dependency formats commonly use one-based real
token identifiers and `0` for the artificial root; adapting that convention belongs at the I/O
boundary, not in this zero-based dynamic-programming kernel.

For `n` tokens, `insideChart` uses four values per inclusive span and runs in `O(n^3)` time and
`O(n^2)` space. Only operations are required at runtime. Algebraic laws are deliberately absent
from the kernel signature, so exact carriers and operational carriers can share the recurrence
without making unsupported claims about floating-point arithmetic.

The deduction follows Jason Eisner, “Three New Probabilistic Models for Dependency Parsing: An
Exploration” (COLING 1996): https://aclanthology.org/C96-1058/.
-/

namespace Nlp.Dependency.Eisner

/-- Collapsed weights for artificial-root and real-token dependency arcs. -/
structure ArcWeights (K : Type u) where
  /-- Number of real tokens. Internal token identifiers are zero-based. -/
  n : Nat
  /-- Weight of choosing `dependent` as the unique child of the artificial root. -/
  rootWeight : Nat → K
  /-- Weight of the real-token arc `head → dependent`; the kernel never requests a self arc. -/
  tokenWeight : Nat → Nat → K

namespace ArcWeights

/-- Safely read an artificial-root weight using the kernel's zero-based token convention. -/
@[inline] def rootWeight? (weights : ArcWeights K) (dependent : Nat) : Option K :=
  if dependent < weights.n then some (weights.rootWeight dependent) else none

/-- Safely read a non-self token arc using the kernel's zero-based token convention. -/
@[inline] def tokenWeight? (weights : ArcWeights K) (head dependent : Nat) : Option K :=
  if head < weights.n && dependent < weights.n && head != dependent then
    some (weights.tokenWeight head dependent)
  else
    none

/-- Map every arc weight without changing token identity or root candidates. -/
def map (f : K → L) (weights : ArcWeights K) : ArcWeights L where
  n := weights.n
  rootWeight := fun dependent ↦ f (weights.rootWeight dependent)
  tokenWeight := fun head dependent ↦ f (weights.tokenWeight head dependent)

@[simp] theorem map_n (f : K → L) (weights : ArcWeights K) :
    (weights.map f).n = weights.n := rfl

@[simp] theorem map_rootWeight (f : K → L) (weights : ArcWeights K) (dependent : Nat) :
    (weights.map f).rootWeight dependent = f (weights.rootWeight dependent) := rfl

@[simp] theorem map_tokenWeight (f : K → L) (weights : ArcWeights K)
    (head dependent : Nat) :
    (weights.map f).tokenWeight head dependent = f (weights.tokenWeight head dependent) := rfl

theorem rootWeight?_eq_some (weights : ArcWeights K) {dependent : Nat}
    (inBounds : dependent < weights.n) :
    weights.rootWeight? dependent = some (weights.rootWeight dependent) := by
  simp [rootWeight?, inBounds]

theorem rootWeight?_eq_none (weights : ArcWeights K) {dependent : Nat}
    (outOfBounds : weights.n ≤ dependent) : weights.rootWeight? dependent = none := by
  simp [rootWeight?, outOfBounds]

theorem tokenWeight?_eq_some (weights : ArcWeights K) {head dependent : Nat}
    (headInBounds : head < weights.n) (dependentInBounds : dependent < weights.n)
    (distinct : head ≠ dependent) :
    weights.tokenWeight? head dependent = some (weights.tokenWeight head dependent) := by
  simp [tokenWeight?, headInBounds, dependentInBounds, distinct]

theorem tokenWeight?_eq_none_of_self (weights : ArcWeights K) {token : Nat} :
    weights.tokenWeight? token token = none := by
  simp [tokenWeight?]

end ArcWeights

/-- The four Eisner items for an inclusive real-token span `[left, right]`. -/
inductive Item where
  /-- Complete subtree whose head is the right endpoint, so dependents extend left. -/
  | completeLeft
  /-- Complete subtree whose head is the left endpoint, so dependents extend right. -/
  | completeRight
  /-- Incomplete subtree containing the arc from the right endpoint to the left endpoint. -/
  | incompleteLeft
  /-- Incomplete subtree containing the arc from the left endpoint to the right endpoint. -/
  | incompleteRight
  deriving Repr, DecidableEq, Inhabited

namespace Item

/-- Stable storage ordinal for one of the four item shapes. -/
@[inline] def offset : Item → Nat
  | .completeLeft => 0
  | .completeRight => 1
  | .incompleteLeft => 2
  | .incompleteRight => 3

theorem offset_lt (item : Item) : item.offset < 4 := by
  cases item <;> decide

end Item

/-- Number of item values stored for every inclusive token span. -/
def itemCount : Nat := 4

/-- Number of scalar entries in an Eisner chart over `n` real tokens. -/
@[inline] def entryCount (n : Nat) : Nat := ChartLayout.entryCount n itemCount

/-- Flat storage index for one inclusive span and item. -/
@[inline] def flatIndex (n left right : Nat) (item : Item) : Nat :=
  ChartLayout.cidx n itemCount left (right + 1) item.offset

/-- Every valid inclusive span/item address lies inside the Eisner chart allocation. -/
theorem flatIndex_lt {n left right : Nat} (item : Item) (ordered : left ≤ right)
    (rightInBounds : right < n) : flatIndex n left right item < entryCount n := by
  exact ChartLayout.cidx_lt_entryCount (by omega) (by omega) item.offset_lt

/-- Dense four-item chart indexed by the number of real tokens at the type level. -/
structure Chart (K : Type u) (n : Nat) where
  private mk ::
  values : Array K
  hsize : values.size = entryCount n

namespace Chart

/-- Number of scalar values retained by a chart. -/
@[inline] def storageSize (chart : Chart K n) : Nat := chart.values.size

@[simp] theorem storageSize_eq (chart : Chart K n) : chart.storageSize = entryCount n :=
  chart.hsize

/-- Safely read one item from a valid inclusive span. -/
@[inline] def value? (chart : Chart K n) (item : Item) (left right : Nat) : Option K :=
  if valid : left ≤ right ∧ right < n then
    some <| chart.values[flatIndex n left right item]'(by
      rw [chart.hsize]
      exact flatIndex_lt item valid.1 valid.2)
  else
    none

/-- Read a complete item whose head is the left endpoint. -/
@[inline] def completeHeadLeft? (chart : Chart K n) (left right : Nat) : Option K :=
  chart.value? .completeRight left right

/-- Read a complete item whose head is the right endpoint. -/
@[inline] def completeHeadRight? (chart : Chart K n) (left right : Nat) : Option K :=
  chart.value? .completeLeft left right

/-- Read an incomplete item containing the arc from the left endpoint to the right endpoint. -/
@[inline] def incompleteHeadLeft? (chart : Chart K n) (left right : Nat) : Option K :=
  chart.value? .incompleteRight left right

/-- Read an incomplete item containing the arc from the right endpoint to the left endpoint. -/
@[inline] def incompleteHeadRight? (chart : Chart K n) (left right : Nat) : Option K :=
  chart.value? .incompleteLeft left right

@[inline] private def empty [Zero K] (n : Nat) : Chart K n where
  values := Array.replicate (entryCount n) 0
  hsize := by simp [entryCount]

@[inline] private def value [Zero K] (chart : Chart K n)
    (item : Item) (left right : Nat) : K :=
  chart.values.getD (flatIndex n left right item) 0

@[inline] private def setValue (chart : Chart K n) (item : Item)
    (left right : Nat) (value : K) : Chart K n where
  values := chart.values.set! (flatIndex n left right item) value
  hsize := by simp [chart.hsize]

end Chart

/--
Fill the four Eisner items for every inclusive real-token span.

Incomplete items combine two adjacent complete items and then apply their endpoint arc. Complete
items attach one incomplete item to a complete remainder. Span width is the topological order, so
every value read by a recurrence has already been finalized.
-/
@[specialize]
def insideChart {K : Type u} [SemiringOps K] (weights : ArcWeights K) :
    Chart K weights.n := Id.run do
  let mut chart := Chart.empty weights.n
  for token in [0:weights.n] do
    chart := chart.setValue .completeRight token token 1
    chart := chart.setValue .completeLeft token token 1
  for width in [2:weights.n + 1] do
    for left in [0:weights.n + 1 - width] do
      let right := left + width - 1
      let leftArc := weights.tokenWeight left right
      let rightArc := weights.tokenWeight right left
      let mut incompleteLeft : K := 0
      let mut incompleteRight : K := 0
      for split in [left:right] do
        let children :=
          chart.value .completeRight left split *
            chart.value .completeLeft (split + 1) right
        incompleteLeft := incompleteLeft + children * leftArc
        incompleteRight := incompleteRight + children * rightArc
      chart := chart.setValue .incompleteRight left right incompleteLeft
      chart := chart.setValue .incompleteLeft left right incompleteRight

      let mut completeLeft : K := 0
      for split in [left + 1:right + 1] do
        completeLeft := completeLeft +
          chart.value .incompleteRight left split *
            chart.value .completeRight split right
      chart := chart.setValue .completeRight left right completeLeft

      let mut completeRight : K := 0
      for split in [left:right] do
        completeRight := completeRight +
          chart.value .completeLeft left split *
            chart.value .incompleteLeft split right
      chart := chart.setValue .completeLeft left right completeRight
  return chart

/-- Contribution of one candidate unique root, or zero when its identifier is out of range. -/
def rootContribution [SemiringOps K] (weights : ArcWeights K)
    (chart : Chart K weights.n) (root : Nat) : K :=
  if root < weights.n then
    (chart.value .completeLeft 0 root *
        chart.value .completeRight root (weights.n - 1)) *
      weights.rootWeight root
  else
    0

/--
Select exactly one artificial-root child from a completed four-item chart.

The empty sentence has no dependency tree. The singleton case copies its root-arc weight exactly,
without introducing operational `1 * weight` computations on carriers whose laws are not assumed.
-/
def goalFromChart [SemiringOps K] (weights : ArcWeights K)
    (chart : Chart K weights.n) : K :=
  if weights.n = 0 then
    0
  else if weights.n = 1 then
    weights.rootWeight 0
  else Id.run do
    let mut total : K := 0
    for root in [0:weights.n] do
      total := total + rootContribution weights chart root
    return total

/-- Single-root projective inside value for collapsed dependency arc weights. -/
@[specialize]
def inside {K : Type u} [SemiringOps K] (weights : ArcWeights K) : K :=
  goalFromChart weights (insideChart weights)

@[simp] theorem goalFromChart_empty [SemiringOps K]
    (weights : ArcWeights K) (chart : Chart K weights.n) (empty : weights.n = 0) :
    goalFromChart weights chart = 0 := by
  simp [goalFromChart, empty]

@[simp] theorem goalFromChart_singleton [SemiringOps K]
    (weights : ArcWeights K) (chart : Chart K weights.n) (singleton : weights.n = 1) :
    goalFromChart weights chart = weights.rootWeight 0 := by
  simp [goalFromChart, singleton]

@[simp] theorem inside_empty [SemiringOps K]
    (rootWeight : Nat → K) (tokenWeight : Nat → Nat → K) :
    inside ({ n := 0, rootWeight, tokenWeight } : ArcWeights K) = 0 := by
  simp [inside]

@[simp] theorem inside_singleton [SemiringOps K]
    (rootWeight : Nat → K) (tokenWeight : Nat → Nat → K) :
    inside ({ n := 1, rootWeight, tokenWeight } : ArcWeights K) = rootWeight 0 := by
  simp [inside]

end Nlp.Dependency.Eisner
