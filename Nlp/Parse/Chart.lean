/-!
# Dense triangular charts

Spans are fencepost intervals `[i, j)` with `0 ≤ i < j ≤ n`.  Cells are ordered by
increasing width and then by their left fencepost, matching the CKY sweep order.
-/

namespace Nlp.Parse.Chart

/-- The number of non-empty spans over a sentence of length `n`. -/
@[inline] def cellCount (n : Nat) : Nat := n * (n + 1) / 2

/-- The number of scalar entries in a dense chart with `nNT` entries per span. -/
@[inline] def entryCount (n nNT : Nat) : Nat := cellCount n * nNT

/-- Offset of the first span having width `width` in a width-major triangular chart. -/
@[inline] def triOff (n width : Nat) : Nat :=
  (width - 1) * (n + 1) - ((width - 1) * width) / 2

/-- Index of the span `[i, j)` in a width-major triangular chart. -/
@[inline] def tri (n i j : Nat) : Nat := triOff n (j - i) + i

/-- Flat index of nonterminal `nonterminal` in the cell for `[i, j)`. -/
@[inline] def cidx (n nNT i j nonterminal : Nat) : Nat :=
  tri n i j * nNT + nonterminal

end Nlp.Parse.Chart
