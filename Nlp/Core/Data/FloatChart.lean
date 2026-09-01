import Nlp.Core.Data.ChartLayout
import Nlp.Core.Data.FloatArrayExt

/-!
# Unboxed dense triangular charts

`FloatChart` stores every non-empty fencepost span `[i, j)` and nonterminal in one unboxed
`FloatArray`.  It shares the dependency-light width-major layout in `Nlp.ChartLayout` and
carries the exact storage-size invariant.

The public boundary is intentionally total and explicit: callers either provide proofs that the
span and nonterminal are valid or use the `Option`-returning operations.  No invalid span silently
aliases a valid cell or turns into an unchecked update.
-/

namespace Nlp

/-- A dense width-major triangular chart backed by unboxed float storage. -/
structure FloatChart where
  n : Nat
  nNT : Nat
  cells : FloatArray
  hsize : cells.size = ChartLayout.entryCount n nNT

namespace FloatChart

/-- The number of non-empty spans over a sentence of length `n`. -/
@[inline] def spanCount (n : Nat) : Nat := ChartLayout.cellCount n

/-- The number of scalar entries in a chart. -/
@[inline] def entryCount (n nNT : Nat) : Nat := ChartLayout.entryCount n nNT

/-- A valid chart address consists of a non-empty in-range span and an in-range nonterminal. -/
def Valid (chart : FloatChart) (i j nonterminal : Nat) : Prop :=
  i < j ∧ j ≤ chart.n ∧ nonterminal < chart.nNT

/-- Allocate every chart entry with the same default value. -/
def empty (n nNT : Nat) (default : Float) : FloatChart where
  n := n
  nNT := nNT
  cells := FloatArray.replicate (entryCount n nNT) default
  hsize := by simp [entryCount]

@[inline] private def flatIndex (chart : FloatChart) (i j nonterminal : Nat) : Nat :=
  ChartLayout.cidx chart.n chart.nNT i j nonterminal

private theorem flatIndex_lt (chart : FloatChart) {i j nonterminal : Nat}
    (spanNonempty : i < j) (spanInBounds : j ≤ chart.n)
    (nonterminalInBounds : nonterminal < chart.nNT) :
    flatIndex chart i j nonterminal < chart.cells.size := by
  rw [chart.hsize]
  exact ChartLayout.cidx_lt_entryCount spanNonempty spanInBounds nonterminalInBounds

/-- Return the flat storage index exactly when the chart address is valid. -/
@[inline] def index? (chart : FloatChart) (i j nonterminal : Nat) : Option Nat :=
  if _spanNonempty : i < j then
    if _spanInBounds : j ≤ chart.n then
      if _nonterminalInBounds : nonterminal < chart.nNT then
        some (flatIndex chart i j nonterminal)
      else
        none
    else
      none
  else
    none

/-- Read a cell using explicit validity proofs. -/
@[inline] def get (chart : FloatChart) (i j nonterminal : Nat)
    (spanNonempty : i < j) (spanInBounds : j ≤ chart.n)
    (nonterminalInBounds : nonterminal < chart.nNT) : Float :=
  chart.cells.get (flatIndex chart i j nonterminal)
    (flatIndex_lt chart spanNonempty spanInBounds nonterminalInBounds)

/-- Read a cell when the span and nonterminal are valid, returning `none` otherwise. -/
@[inline] def get? (chart : FloatChart) (i j nonterminal : Nat) : Option Float :=
  if spanNonempty : i < j then
    if spanInBounds : j ≤ chart.n then
      if nonterminalInBounds : nonterminal < chart.nNT then
        some (chart.get i j nonterminal spanNonempty spanInBounds nonterminalInBounds)
      else
        none
    else
      none
  else
    none

/--
Update a valid cell and preserve the size invariant.

The chart and its `FloatArray` are consumed by value; when they have a single owner, Lean's
reference-counting runtime performs the primitive `FloatArray.set` update in place.
-/
@[inline] def set (chart : FloatChart) (i j nonterminal : Nat) (value : Float)
    (spanNonempty : i < j) (spanInBounds : j ≤ chart.n)
    (nonterminalInBounds : nonterminal < chart.nNT) : FloatChart :=
  { chart with
    cells := chart.cells.set (flatIndex chart i j nonterminal) value
      (flatIndex_lt chart spanNonempty spanInBounds nonterminalInBounds)
    hsize := by
      rw [FloatArray.size_set]
      exact chart.hsize }

/-- Update a cell when its address is valid, returning `none` otherwise. -/
@[inline] def set? (chart : FloatChart) (i j nonterminal : Nat)
    (value : Float) : Option FloatChart :=
  if spanNonempty : i < j then
    if spanInBounds : j ≤ chart.n then
      if nonterminalInBounds : nonterminal < chart.nNT then
        some (chart.set i j nonterminal value spanNonempty spanInBounds nonterminalInBounds)
      else
        none
    else
      none
  else
    none

end FloatChart

end Nlp
