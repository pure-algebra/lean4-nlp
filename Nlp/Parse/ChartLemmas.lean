import Nlp.Parse.Chart

/-!
# Correctness of the triangular chart layout

`Nlp.Parse.Chart` packs the `n * (n + 1) / 2` spans of a length-`n` sentence into a flat array,
width-major.  This module proves the two facts every chart client relies on:

* **bounds** — every valid span/nonterminal pair lands strictly inside the allocated array
  (`tri_lt_cellCount`, `cidx_lt_entryCount`), so the kernels' `set!`/`getD` never hit the
  out-of-bounds fallback; and
* **injectivity** — distinct span/nonterminal pairs land at distinct indices (`tri_inj`,
  `cidx_inj`), so chart updates never alias.

The arithmetic burden is the triangular offset `triOff n w = (w-1)*(n+1) - (w-1)*w/2`.  All
division-by-two reasoning is confined to `two_dvd_mul_succ` and the successor recurrence
`triOff_succ`; everything else is linear arithmetic over those facts.
-/

namespace Nlp.Parse.Chart

@[simp] theorem triOff_one (n : Nat) : triOff n 1 = 0 :=
  Nlp.ChartLayout.triOff_one n

/-- The successor recurrence: the width-`w` band holds `n + 1 - w` spans, and the next band
starts right after it. -/
theorem triOff_succ (n w : Nat) (h1 : 1 ≤ w) (hw : w ≤ n) :
    triOff n (w + 1) = triOff n w + (n + 1 - w) :=
  Nlp.ChartLayout.triOff_succ n w h1 hw

/-- Band offsets grow with the width. -/
theorem triOff_mono (n w w' : Nat) (h1 : 1 ≤ w) (hww' : w ≤ w') (hw' : w' ≤ n + 1) :
    triOff n w ≤ triOff n w' :=
  Nlp.ChartLayout.triOff_mono n w w' h1 hww' hw'

/-- The band past the widest possible span starts exactly at the end of the chart. -/
theorem triOff_last (n : Nat) : triOff n (n + 1) = cellCount n :=
  Nlp.ChartLayout.triOff_last n

/-- Every valid span's cell index is inside the allocated triangle. -/
theorem tri_lt_cellCount {n i j : Nat} (hij : i < j) (hjn : j ≤ n) :
    tri n i j < cellCount n :=
  Nlp.ChartLayout.tri_lt_cellCount hij hjn

/-- A strictly narrower valid span sits strictly earlier in the width-major order. -/
theorem tri_lt_of_width_lt {n i j i' j' : Nat} (hij : i < j) (hjn : j ≤ n)
    (hi'j' : i' < j') (hj'n : j' ≤ n) (hww : j - i < j' - i') :
    tri n i j < tri n i' j' :=
  Nlp.ChartLayout.tri_lt_of_width_lt hij hjn hi'j' hj'n hww

/-- Distinct valid spans have distinct cell indices. -/
theorem tri_inj {n i j i' j' : Nat} (hij : i < j) (hjn : j ≤ n)
    (hi'j' : i' < j') (hj'n : j' ≤ n) (h : tri n i j = tri n i' j') :
    i = i' ∧ j = j' :=
  Nlp.ChartLayout.tri_inj hij hjn hi'j' hj'n h

/-- Every valid span/nonterminal pair's flat index is inside the allocated chart. -/
theorem cidx_lt_entryCount {n nNT i j a : Nat} (hij : i < j) (hjn : j ≤ n) (ha : a < nNT) :
    cidx n nNT i j a < entryCount n nNT :=
  Nlp.ChartLayout.cidx_lt_entryCount hij hjn ha

/-- Distinct valid span/nonterminal pairs never alias in the flat chart. -/
theorem cidx_inj {n nNT i j i' j' a a' : Nat} (hij : i < j) (hjn : j ≤ n)
    (hi'j' : i' < j') (hj'n : j' ≤ n) (ha : a < nNT) (ha' : a' < nNT)
    (h : cidx n nNT i j a = cidx n nNT i' j' a') :
    i = i' ∧ j = j' ∧ a = a' :=
  Nlp.ChartLayout.cidx_inj hij hjn hi'j' hj'n ha ha' h

end Nlp.Parse.Chart
