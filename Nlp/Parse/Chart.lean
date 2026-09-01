import Nlp.Core.Data.ChartLayout

/-!
# Dense triangular charts

Spans are fencepost intervals `[i, j)` with `0 ≤ i < j ≤ n`.  Cells are ordered by
increasing width and then by their left fencepost, matching the CKY sweep order.
-/

namespace Nlp.Parse.Chart

/-- The number of non-empty spans over a sentence of length `n`. -/
abbrev cellCount (n : Nat) : Nat := Nlp.ChartLayout.cellCount n

/-- The number of scalar entries in a dense chart with `nNT` entries per span. -/
abbrev entryCount (n nNT : Nat) : Nat := Nlp.ChartLayout.entryCount n nNT

/-- Offset of the first span having width `width` in a width-major triangular chart. -/
abbrev triOff (n width : Nat) : Nat := Nlp.ChartLayout.triOff n width

/-- Index of the span `[i, j)` in a width-major triangular chart. -/
abbrev tri (n i j : Nat) : Nat := Nlp.ChartLayout.tri n i j

/-- Flat index of nonterminal `nonterminal` in the cell for `[i, j)`. -/
abbrev cidx (n nNT i j nonterminal : Nat) : Nat :=
  Nlp.ChartLayout.cidx n nNT i j nonterminal

end Nlp.Parse.Chart
