/-!
# Dense triangular chart layout

This dependency-light core module defines the width-major layout shared by boxed and unboxed
charts.  Spans are fencepost intervals `[i, j)` with `0 ≤ i < j ≤ n`; within each width,
cells are ordered by their left fencepost.

The bounds and injectivity theorems keep all division-by-two arithmetic at this layout boundary.
Higher-level parsing modules can reuse the layout without becoming dependencies of core storage.
-/

namespace Nlp.ChartLayout

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

/-- A product of consecutive naturals is even. -/
private theorem two_dvd_mul_succ (a : Nat) : a * (a + 1) % 2 = 0 := by
  induction a with
  | zero => rfl
  | succ k ih =>
    have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by
      rw [Nat.mul_comm (k + 1) (k + 1 + 1), Nat.succ_mul, Nat.succ_mul]; omega
    omega

@[simp] theorem triOff_one (n : Nat) : triOff n 1 = 0 := by
  simp [triOff]

/-- The successor recurrence: the width-`w` band holds `n + 1 - w` spans, and the next band
starts right after it. -/
theorem triOff_succ (n w : Nat) (h1 : 1 ≤ w) (hw : w ≤ n) :
    triOff n (w + 1) = triOff n w + (n + 1 - w) := by
  obtain ⟨a, rfl⟩ : ∃ a, w = a + 1 := ⟨w - 1, by omega⟩
  simp only [triOff, Nat.add_sub_cancel]
  have h2 : (a + 1) * (n + 1) = a * (n + 1) + (n + 1) := Nat.succ_mul a (n + 1)
  have h3 : (a + 1) * (a + 1 + 1) = a * (a + 1) + 2 * (a + 1) := by
    rw [Nat.mul_comm (a + 1) (a + 1 + 1), Nat.succ_mul, Nat.succ_mul]; omega
  have h4 : a * (a + 1) % 2 = 0 := two_dvd_mul_succ a
  have h5 : a * (a + 1) ≤ a * (n + 1) := Nat.mul_le_mul_left a (by omega)
  omega

/-- Band offsets grow with the width. -/
theorem triOff_mono (n w w' : Nat) (h1 : 1 ≤ w) (hww' : w ≤ w') (hw' : w' ≤ n + 1) :
    triOff n w ≤ triOff n w' := by
  induction w' with
  | zero => omega
  | succ v ih =>
    rcases Nat.lt_or_ge w (v + 1) with hlt | hge
    · have hwv : w ≤ v := by omega
      have hstep : triOff n v ≤ triOff n (v + 1) := by
        rw [triOff_succ n v (Nat.le_trans h1 hwv) (by omega)]
        exact Nat.le_add_right _ _
      exact Nat.le_trans (ih hwv (by omega)) hstep
    · have heq : w = v + 1 := by omega
      subst heq
      exact Nat.le_refl _

/-- The band past the widest possible span starts exactly at the end of the chart. -/
theorem triOff_last (n : Nat) : triOff n (n + 1) = cellCount n := by
  have h := two_dvd_mul_succ n
  simp only [triOff, cellCount, Nat.add_sub_cancel]
  omega

/-- Every valid span's cell index is inside the allocated triangle. -/
theorem tri_lt_cellCount {n i j : Nat} (hij : i < j) (hjn : j ≤ n) :
    tri n i j < cellCount n := by
  have hband : tri n i j < triOff n (j - i + 1) := by
    rw [triOff_succ n (j - i) (by omega) (by omega)]
    show triOff n (j - i) + i < triOff n (j - i) + (n + 1 - (j - i))
    omega
  have hmono : triOff n (j - i + 1) ≤ triOff n (n + 1) :=
    triOff_mono n (j - i + 1) (n + 1) (by omega) (by omega) (Nat.le_refl _)
  exact Nat.lt_of_lt_of_le hband (triOff_last n ▸ hmono)

/-- A strictly narrower valid span sits strictly earlier in the width-major order. -/
theorem tri_lt_of_width_lt {n i j i' j' : Nat} (hij : i < j) (hjn : j ≤ n)
    (hi'j' : i' < j') (hj'n : j' ≤ n) (hww : j - i < j' - i') :
    tri n i j < tri n i' j' := by
  have hband : tri n i j < triOff n (j - i + 1) := by
    rw [triOff_succ n (j - i) (by omega) (by omega)]
    show triOff n (j - i) + i < triOff n (j - i) + (n + 1 - (j - i))
    omega
  have hmono : triOff n (j - i + 1) ≤ triOff n (j' - i') :=
    triOff_mono n (j - i + 1) (j' - i') (by omega) (by omega) (by omega)
  exact Nat.lt_of_lt_of_le hband (Nat.le_trans hmono (Nat.le_add_right _ i'))

/-- Distinct valid spans have distinct cell indices. -/
theorem tri_inj {n i j i' j' : Nat} (hij : i < j) (hjn : j ≤ n)
    (hi'j' : i' < j') (hj'n : j' ≤ n) (h : tri n i j = tri n i' j') :
    i = i' ∧ j = j' := by
  rcases Nat.lt_trichotomy (j - i) (j' - i') with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (tri_lt_of_width_lt hij hjn hi'j' hj'n hlt))
  · have hoff : triOff n (j' - i') + i = triOff n (j' - i') + i' := by
      have : triOff n (j - i) + i = triOff n (j' - i') + i' := h
      rw [heq] at this
      exact this
    omega
  · exact absurd h.symm (Nat.ne_of_lt (tri_lt_of_width_lt hi'j' hj'n hij hjn hgt))

/-- Split a flat `cell * count + entry` index into its unique quotient/remainder pair. -/
private theorem flat_inj {d t t' r r' : Nat} (hr : r < d) (hr' : r' < d)
    (h : t * d + r = t' * d + r') : t = t' ∧ r = r' := by
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have ht : t = t' := by
    have hdiv := congrArg (· / d) h
    simpa [Nat.mul_comm t d, Nat.mul_comm t' d, Nat.mul_add_div hd,
      Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr'] using hdiv
  subst ht
  exact ⟨rfl, by omega⟩

/-- Every valid span/nonterminal pair's flat index is inside the allocated chart. -/
theorem cidx_lt_entryCount {n nNT i j a : Nat} (hij : i < j) (hjn : j ≤ n) (ha : a < nNT) :
    cidx n nNT i j a < entryCount n nNT := by
  have htri : tri n i j < cellCount n := tri_lt_cellCount hij hjn
  show tri n i j * nNT + a < cellCount n * nNT
  calc tri n i j * nNT + a < tri n i j * nNT + nNT := by omega
    _ = (tri n i j + 1) * nNT := (Nat.succ_mul _ _).symm
    _ ≤ cellCount n * nNT := Nat.mul_le_mul_right nNT htri

/-- Distinct valid span/nonterminal pairs never alias in the flat chart. -/
theorem cidx_inj {n nNT i j i' j' a a' : Nat} (hij : i < j) (hjn : j ≤ n)
    (hi'j' : i' < j') (hj'n : j' ≤ n) (ha : a < nNT) (ha' : a' < nNT)
    (h : cidx n nNT i j a = cidx n nNT i' j' a') :
    i = i' ∧ j = j' ∧ a = a' := by
  obtain ⟨htri, haa⟩ := flat_inj ha ha' h
  obtain ⟨hii, hjj⟩ := tri_inj hij hjn hi'j' hj'n htri
  exact ⟨hii, hjj, haa⟩

end Nlp.ChartLayout
