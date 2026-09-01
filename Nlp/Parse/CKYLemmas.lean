import Nlp.Core.Algebra.BigOps
import Nlp.Parse.CKY

/-!
# Functional restatement of the dense CKY kernel

`Nlp.Parse.ckyNaive` is the imperative reference parser.  This module proves that it equals a
tower of plain `List.foldl`s over the same index ranges (`ckyNaive_eq_fold`), so chart-content
reasoning can proceed by induction on rules and spans rather than loop reasoning.  As a first
consequence, the chart always has exactly `Chart.entryCount` entries (`ckyNaive_size`), which
together with `goalIndex_lt_entryCount` shows that `ckyNaiveGoal` reads a genuinely computed
cell.

The fold shapes (including the residual `i + width - (i + 1)` split count) mirror the loop
normal forms exactly, so the refinement theorem is definitional once the `Id`/`forIn`
scaffolding is rewritten away.
-/

namespace Nlp.Parse

variable {K : Type} [SemiringOps K] [Inhabited K]

/-- Fold one lexical pass for word position `i` into the chart. -/
def lexStep (grammar : CNF K) (words : Array Tok) (chart : Array K) (i : Nat) : Array K :=
  grammar.lex.foldl
    (fun chart rule ↦
      if rule.tok == words[i]! && rule.lhs.toNat < grammar.nNT then
        chart.set! (Chart.cidx words.size grammar.nNT i (i + 1) rule.lhs.toNat)
          (chart[Chart.cidx words.size grammar.nNT i (i + 1) rule.lhs.toNat]! + rule.w)
      else chart)
    chart

/-- Fold every binary rule for the split `(i, split, j)` into the chart. -/
def binStep (grammar : CNF K) (words : Array Tok) (i j split : Nat) (chart : Array K) :
    Array K :=
  grammar.bin.foldl
    (fun chart rule ↦
      if IndexedCNF.ruleInBounds grammar.nNT rule then
        chart.set! (Chart.cidx words.size grammar.nNT i j rule.lhs.toNat)
          (chart[Chart.cidx words.size grammar.nNT i j rule.lhs.toNat]! +
            rule.w * chart[Chart.cidx words.size grammar.nNT i split rule.r1.toNat]! *
              chart[Chart.cidx words.size grammar.nNT split j rule.r2.toNat]!)
      else chart)
    chart

/-- Functional restatement of the dense CKY sweep. -/
def ckyNaiveFold (grammar : CNF K) (words : Array Tok) : Array K :=
  (List.range' 2 (words.size + 1 - 2)).foldl
    (fun chart width ↦
      (List.range (words.size + 1 - width)).foldl
        (fun chart i ↦
          (List.range' (i + 1) (i + width - (i + 1))).foldl
            (fun chart split ↦ binStep grammar words i (i + width) split chart)
            chart)
        chart)
    ((List.range words.size).foldl (lexStep grammar words)
      (Array.replicate (Chart.entryCount words.size grammar.nNT) 0))

private theorem id_pure_eq {α : Type v} (a : α) : (pure a : Id α) = a := rfl

private theorem id_bind_eq {α β : Type v} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

private theorem id_forIn_range_yield_eq_foldl {β : Type w} (r : Std.Legacy.Range)
    (f : Nat → β → β) (init : β) :
    (forIn (m := Id) r init fun a b ↦ ForInStep.yield (f a b)) =
      (List.range' r.start r.size r.step).foldl (fun b a ↦ f a b) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact List.forIn_pure_yield_eq_foldl f init

private theorem id_forIn_arr_yield_eq_foldl {α : Type v} {β : Type w} (xs : Array α)
    (f : α → β → β) (init : β) :
    (forIn (m := Id) xs init fun a b ↦ ForInStep.yield (f a b)) =
      xs.foldl (fun b a ↦ f a b) init :=
  Array.forIn_pure_yield_eq_foldl f init

private theorem ite_yield {β : Type v} (c : Prop) [inst : Decidable c] (x y : β) :
    @ite (Id (ForInStep β)) c inst (ForInStep.yield x) (ForInStep.yield y) =
      ForInStep.yield (if c then x else y) := by
  split <;> rfl

/-- **Kernel refinement.**  The imperative dense CKY sweep is the functional fold tower. -/
theorem ckyNaive_eq_fold (grammar : CNF K) (words : Array Tok) :
    ckyNaive grammar words = ckyNaiveFold grammar words := by
  unfold ckyNaive
  simp only [Id.run, id_bind_eq, id_pure_eq, ite_yield, id_forIn_range_yield_eq_foldl,
    id_forIn_arr_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, ← List.range_eq_range']
  rfl

omit [SemiringOps K] [Inhabited K] in
private theorem foldl_size_invariant {α : Type v} (l : List α) (f : Array K → α → Array K)
    (h : ∀ chart a, (f chart a).size = chart.size) (chart : Array K) :
    (l.foldl f chart).size = chart.size := by
  induction l generalizing chart with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, h]

private theorem lexStep_size (grammar : CNF K) (words : Array Tok) (chart : Array K) (i : Nat) :
    (lexStep grammar words chart i).size = chart.size := by
  unfold lexStep
  rw [← Array.foldl_toList]
  refine foldl_size_invariant _ _ (fun chart rule ↦ ?_) chart
  split
  · simp [Array.set!]
  · rfl

private theorem binStep_size (grammar : CNF K) (words : Array Tok) (i j split : Nat)
    (chart : Array K) : (binStep grammar words i j split chart).size = chart.size := by
  unfold binStep
  rw [← Array.foldl_toList]
  refine foldl_size_invariant _ _ (fun chart rule ↦ ?_) chart
  split
  · simp [Array.set!]
  · rfl

/-- The functional chart always has one entry per span/nonterminal pair. -/
theorem ckyNaiveFold_size (grammar : CNF K) (words : Array Tok) :
    (ckyNaiveFold grammar words).size = Chart.entryCount words.size grammar.nNT := by
  unfold ckyNaiveFold
  rw [foldl_size_invariant _ _
      (fun chart width ↦
        foldl_size_invariant _ _
          (fun chart i ↦
            foldl_size_invariant _ _
              (fun chart split ↦ binStep_size grammar words i (i + width) split chart) chart)
          chart),
    foldl_size_invariant _ _ (fun chart i ↦ lexStep_size grammar words chart i)]
  exact Array.size_replicate

/-- The imperative reference chart always has one entry per span/nonterminal pair.  Together
with `goalIndex_lt_entryCount` this shows `ckyNaiveGoal` reads a computed cell, never the
`getD` fallback. -/
theorem ckyNaive_size (grammar : CNF K) (words : Array Tok) :
    (ckyNaive grammar words).size = Chart.entryCount words.size grammar.nNT :=
  (ckyNaive_eq_fold grammar words) ▸ ckyNaiveFold_size grammar words

/-! ## Lexical-layer correctness

Each width-1 cell of the reference chart is exactly the fold, in rule order, of the weights of
the lexical rules matching that position and nonterminal.  The accumulation order matches the
kernel's, so no algebraic laws are needed.  The proof splits the sweep into: positions before
`i` (preserve the cell), position `i` (accumulate), positions after `i` (preserve), and the
binary passes (write only cells of width ≥ 2, so preserve by chart-index injectivity).
-/

omit [Inhabited K] in
private theorem foldl_getD_invariant {α : Type v} (l : List α) (f : Array K → α → Array K)
    (idx : Nat) (h : ∀ chart, ∀ a ∈ l, (f chart a).getD idx 0 = chart.getD idx 0)
    (chart : Array K) : (l.foldl f chart).getD idx 0 = chart.getD idx 0 := by
  induction l generalizing chart with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih fun c a ha ↦ h c a (List.mem_cons_of_mem x ha),
      h chart x List.mem_cons_self]

private theorem setAdd_getD_ne (chart : Array K) (t t' : Nat) (w : K) (h : t' ≠ t) :
    (chart.set! t' (chart[t']! + w)).getD t 0 = chart.getD t 0 := by
  simp [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

private theorem setAdd_getD_self (chart : Array K) (t : Nat) (w : K) (h : t < chart.size) :
    (chart.set! t (chart[t]! + w)).getD t 0 = chart.getD t 0 + w := by
  simp [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt h,
    Array.getElem!_eq_getD, Array.getElem?_eq_getElem h]

/-- The weight the lexical layer owes cell `(i, i + 1, a)`: the matching rules, in rule order. -/
def lexCellSum (grammar : CNF K) (words : Array Tok) (i a : Nat) : K :=
  grammar.lex.toList.foldl
    (fun acc rule ↦ if rule.tok == words[i]! ∧ rule.lhs.toNat = a then acc + rule.w else acc) 0

private theorem lexList_getD (rules : List (LexRule K)) (words : Array Tok) (nNT i a : Nat)
    (hi : i < words.size) (ha : a < nNT) :
    ∀ chart : Array K, chart.size = Chart.entryCount words.size nNT →
      (rules.foldl
          (fun chart rule ↦
            if rule.tok == words[i]! && rule.lhs.toNat < nNT then
              chart.set! (Chart.cidx words.size nNT i (i + 1) rule.lhs.toNat)
                (chart[Chart.cidx words.size nNT i (i + 1) rule.lhs.toNat]! + rule.w)
            else chart)
          chart).getD (Chart.cidx words.size nNT i (i + 1) a) 0 =
        rules.foldl
          (fun acc rule ↦ if rule.tok == words[i]! ∧ rule.lhs.toNat = a then acc + rule.w else acc)
          (chart.getD (Chart.cidx words.size nNT i (i + 1) a) 0) := by
  induction rules with
  | nil => intro chart _; rfl
  | cons r rs ih =>
    intro chart hsize
    rw [List.foldl_cons, List.foldl_cons]
    by_cases htok : (r.tok == words[i]!) = true
    · by_cases hlhs : r.lhs.toNat = a
      · subst hlhs
        rw [if_pos (by simp [htok, ha]), if_pos ⟨htok, rfl⟩,
          ih _ (by rw [Array.size_set!]; exact hsize),
          setAdd_getD_self _ _ _ (hsize ▸ Chart.cidx_lt_entryCount (Nat.lt_succ_self i) hi ha)]
      · by_cases hbound : r.lhs.toNat < nNT
        · rw [if_pos (by simp [htok, hbound]), if_neg (fun hand ↦ hlhs hand.2),
            ih _ (by rw [Array.size_set!]; exact hsize),
            setAdd_getD_ne _ _ _ _ (fun heq ↦ ?_)]
          obtain ⟨-, -, hAA⟩ :=
            Chart.cidx_inj (Nat.lt_succ_self i) hi (Nat.lt_succ_self i) hi hbound ha heq
          exact hlhs hAA
        · rw [if_neg (by simp [hbound]), if_neg (fun hand ↦ hlhs hand.2), ih _ hsize]
    · rw [if_neg (by simp [htok]), if_neg (fun hand ↦ htok hand.1), ih _ hsize]

private theorem lexStep_getD_ne (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (i' i a : Nat) (hne : i' ≠ i) (hi' : i' < words.size) (hi : i < words.size)
    (ha : a < grammar.nNT) :
    (lexStep grammar words chart i').getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 =
      chart.getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 := by
  unfold lexStep
  rw [← Array.foldl_toList]
  refine foldl_getD_invariant _ _ _ (fun chart rule _ ↦ ?_) chart
  by_cases hguard : (rule.tok == words[i']! && decide (rule.lhs.toNat < grammar.nNT)) = true
  · rw [if_pos hguard]
    refine setAdd_getD_ne _ _ _ _ fun heq ↦ ?_
    have hbound : rule.lhs.toNat < grammar.nNT :=
      of_decide_eq_true ((Bool.and_eq_true _ _).mp hguard).2
    obtain ⟨hii, -, -⟩ :=
      Chart.cidx_inj (Nat.lt_succ_self i') hi' (Nat.lt_succ_self i) hi hbound ha heq
    exact hne hii
  · rw [if_neg hguard]

private theorem binStep_getD_width1 (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (i' width split i a : Nat) (hw : 2 ≤ width) (hspan : i' + width ≤ words.size)
    (hi : i < words.size) (ha : a < grammar.nNT) :
    (binStep grammar words i' (i' + width) split chart).getD
        (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 =
      chart.getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 := by
  unfold binStep
  rw [← Array.foldl_toList]
  refine foldl_getD_invariant _ _ _ (fun chart rule _ ↦ ?_) chart
  by_cases hguard : IndexedCNF.ruleInBounds grammar.nNT rule = true
  · rw [if_pos hguard]
    refine setAdd_getD_ne _ _ _ _ fun heq ↦ ?_
    have hbound : rule.lhs.toNat < grammar.nNT := by
      unfold IndexedCNF.ruleInBounds at hguard
      have := (Bool.and_eq_true _ _).mp hguard
      exact of_decide_eq_true ((Bool.and_eq_true _ _).mp this.1).1
    obtain ⟨hii, hjj, -⟩ :=
      Chart.cidx_inj (by omega : i' < i' + width) hspan (Nat.lt_succ_self i) hi hbound ha heq
    omega
  · rw [if_neg hguard]

/--
**Lexical-layer correctness.**  Every width-1 cell of the reference chart holds exactly the
accumulated weight of the lexical rules matching its position and nonterminal, in rule order.
No algebraic laws are used, so this holds for every `SemiringOps` carrier.
-/
theorem ckyNaive_getD_lex (grammar : CNF K) (words : Array Tok) (i a : Nat)
    (hi : i < words.size) (ha : a < grammar.nNT) :
    (ckyNaive grammar words).getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 =
      lexCellSum grammar words i a := by
  rw [ckyNaive_eq_fold]
  unfold ckyNaiveFold
  -- the binary passes never write a width-1 cell
  have hbin : ∀ (chart : Array K) (width : Nat), width ∈ List.range' 2 (words.size + 1 - 2) →
      ((List.range (words.size + 1 - width)).foldl
          (fun chart i ↦
            (List.range' (i + 1) (i + width - (i + 1))).foldl
              (fun chart split ↦ binStep grammar words i (i + width) split chart) chart)
          chart).getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 =
        chart.getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 := by
    intro chart width hwmem
    obtain ⟨wk, hwk, rfl⟩ := List.mem_range'.mp hwmem
    refine foldl_getD_invariant _ _ _ (fun chart' i' hi'mem ↦ ?_) chart
    have hi'lt := List.mem_range.mp hi'mem
    refine foldl_getD_invariant _ _ _ (fun chart'' split _ ↦ ?_) chart'
    exact binStep_getD_width1 grammar words chart'' i' (2 + 1 * wk) split i a (by omega)
      (by omega) hi ha
  rw [foldl_getD_invariant _ _ _ hbin]
  -- positions other than `i` in the lexical pass preserve the cell
  have hafter : ∀ (chart : Array K) (p : Nat), p ∈ List.range' (i + 1) (words.size - (i + 1)) →
      (lexStep grammar words chart p).getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 =
        chart.getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 := by
    intro chart p hp
    obtain ⟨pk, hpk, rfl⟩ := List.mem_range'.mp hp
    exact lexStep_getD_ne grammar words chart _ i a (by omega) (by omega) hi ha
  have hbefore : ∀ (chart : Array K) (p : Nat), p ∈ List.range' 0 i →
      (lexStep grammar words chart p).getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 =
        chart.getD (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 := by
    intro chart p hp
    obtain ⟨pk, hpk, rfl⟩ := List.mem_range'.mp hp
    exact lexStep_getD_ne grammar words chart _ i a (by omega) (by omega) hi ha
  -- split the position sweep around `i`
  have hsplit : List.range words.size =
      List.range' 0 i ++ i :: List.range' (i + 1) (words.size - (i + 1)) := by
    have h1 : words.size = i + (1 + (words.size - (i + 1))) := by omega
    conv => lhs; rw [List.range_eq_range', h1]
    rw [← List.range'_append_1 (s := 0) (m := i), ← List.range'_append_1 (s := 0 + i) (m := 1)]
    simp [List.range'_succ]
  rw [hsplit, List.foldl_append, List.foldl_cons, foldl_getD_invariant _ _ _ hafter]
  -- the preserved prefix value is the initial zero
  have hpre :
      ((List.range' 0 i).foldl (lexStep grammar words)
          (Array.replicate (Chart.entryCount words.size grammar.nNT) 0)).getD
        (Chart.cidx words.size grammar.nNT i (i + 1) a) 0 = 0 := by
    rw [foldl_getD_invariant _ _ _ hbefore]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have hpresize :
      ((List.range' 0 i).foldl (lexStep grammar words)
          (Array.replicate (Chart.entryCount words.size grammar.nNT) 0)).size =
        Chart.entryCount words.size grammar.nNT := by
    rw [foldl_size_invariant _ _ fun chart p ↦ lexStep_size grammar words chart p]
    exact Array.size_replicate
  have hstep : ∀ chart : Array K,
      lexStep grammar words chart i =
        grammar.lex.toList.foldl
          (fun chart rule ↦
            if rule.tok == words[i]! && rule.lhs.toNat < grammar.nNT then
              chart.set! (Chart.cidx words.size grammar.nNT i (i + 1) rule.lhs.toNat)
                (chart[Chart.cidx words.size grammar.nNT i (i + 1) rule.lhs.toNat]! + rule.w)
            else chart)
          chart := by
    intro chart
    unfold lexStep
    rw [← Array.foldl_toList]
  rw [hstep, lexList_getD grammar.lex.toList words grammar.nNT i a hi ha _ hpresize, hpre]
  rfl

/-! ## Binary-layer correctness

The counterpart of `ckyNaive_getD_lex` for cells of width at least two: each such cell holds
exactly the split/rule accumulation of the Bellman recurrence, with both children read from the
*final* chart.  As before the accumulation order matches the kernel's, so no algebraic laws are
required.  The key structural facts are span-disjointness (a pass writes only its own span's
cells, by chart-index injectivity) and read-stability (child cells are narrower than the cell
being filled, so no later write touches them).
-/

private theorem getElem_bang_eq_getD (chart : Array K) (t : Nat) (h : t < chart.size) :
    chart[t]! = chart.getD t 0 := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]

omit [SemiringOps K] [Inhabited K] in
private theorem foldl_congr_fun {α : Type v} (l : List α) (f g : K → α → K)
    (h : ∀ acc : K, ∀ x ∈ l, f acc x = g acc x) : ∀ acc : K, l.foldl f acc = l.foldl g acc := by
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons, List.foldl_cons, h acc x List.mem_cons_self,
      ih fun a y hy ↦ h a y (List.mem_cons_of_mem x hy)]

private theorem lexStep_getD_ne_span (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (p x y b : Nat) (hp : p < words.size) (hxy : x < y) (hyn : y ≤ words.size)
    (hb : b < grammar.nNT) (hne : ¬(x = p ∧ y = p + 1)) :
    (lexStep grammar words chart p).getD (Chart.cidx words.size grammar.nNT x y b) 0 =
      chart.getD (Chart.cidx words.size grammar.nNT x y b) 0 := by
  unfold lexStep
  rw [← Array.foldl_toList]
  refine foldl_getD_invariant _ _ _ (fun chart rule _ ↦ ?_) chart
  by_cases hguard : (rule.tok == words[p]! && decide (rule.lhs.toNat < grammar.nNT)) = true
  · rw [if_pos hguard]
    refine setAdd_getD_ne _ _ _ _ fun heq ↦ ?_
    have hbound : rule.lhs.toNat < grammar.nNT :=
      of_decide_eq_true ((Bool.and_eq_true _ _).mp hguard).2
    obtain ⟨hxp, hyp, -⟩ := Chart.cidx_inj (Nat.lt_succ_self p) hp hxy hyn hbound hb heq
    exact hne ⟨hxp.symm, hyp.symm⟩
  · rw [if_neg hguard]

omit [SemiringOps K] [Inhabited K] in
private theorem ruleInBounds_decompose {nNT : Nat} {rule : BinRule K}
    (hguard : IndexedCNF.ruleInBounds nNT rule = true) :
    rule.lhs.toNat < nNT ∧ rule.r1.toNat < nNT ∧ rule.r2.toNat < nNT := by
  unfold IndexedCNF.ruleInBounds at hguard
  have h1 := (Bool.and_eq_true _ _).mp hguard
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2, of_decide_eq_true h1.2⟩

private theorem binStep_getD_ne_span (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (i' j' split x y b : Nat) (hij' : i' < j') (hj'n : j' ≤ words.size)
    (hxy : x < y) (hyn : y ≤ words.size) (hb : b < grammar.nNT) (hne : ¬(x = i' ∧ y = j')) :
    (binStep grammar words i' j' split chart).getD
        (Chart.cidx words.size grammar.nNT x y b) 0 =
      chart.getD (Chart.cidx words.size grammar.nNT x y b) 0 := by
  unfold binStep
  rw [← Array.foldl_toList]
  refine foldl_getD_invariant _ _ _ (fun chart rule _ ↦ ?_) chart
  by_cases hguard : IndexedCNF.ruleInBounds grammar.nNT rule = true
  · rw [if_pos hguard]
    refine setAdd_getD_ne _ _ _ _ fun heq ↦ ?_
    obtain ⟨hxi, hyj, -⟩ :=
      Chart.cidx_inj hij' hj'n hxy hyn (ruleInBounds_decompose hguard).1 hb heq
    exact hne ⟨hxi.symm, hyj.symm⟩
  · rw [if_neg hguard]

/-- Cells whose spans sit strictly inside `[i, j)` on either side of a split — exactly the
cells the width pass for `(i, j)` reads. -/
private def AgreesOnChildren (words : Array Tok) (nNT i j : Nat) (chart base : Array K) : Prop :=
  ∀ s b : Nat, i < s → s < j → b < nNT →
    chart.getD (Chart.cidx words.size nNT i s b) 0 =
        base.getD (Chart.cidx words.size nNT i s b) 0 ∧
      chart.getD (Chart.cidx words.size nNT s j b) 0 =
        base.getD (Chart.cidx words.size nNT s j b) 0

private theorem binRules_getD (rules : List (BinRule K)) (words : Array Tok)
    (nNT i j split a : Nat) (hij : i < j) (hjn : j ≤ words.size) (ha : a < nNT)
    (hs1 : i < split) (hs2 : split < j) :
    ∀ chart base : Array K, chart.size = Chart.entryCount words.size nNT →
      AgreesOnChildren words nNT i j chart base →
      (rules.foldl
          (fun chart rule ↦
            if IndexedCNF.ruleInBounds nNT rule then
              chart.set! (Chart.cidx words.size nNT i j rule.lhs.toNat)
                (chart[Chart.cidx words.size nNT i j rule.lhs.toNat]! +
                  rule.w * chart[Chart.cidx words.size nNT i split rule.r1.toNat]! *
                    chart[Chart.cidx words.size nNT split j rule.r2.toNat]!)
            else chart)
          chart).getD (Chart.cidx words.size nNT i j a) 0 =
        rules.foldl
          (fun acc rule ↦
            if IndexedCNF.ruleInBounds nNT rule = true ∧ rule.lhs.toNat = a then
              acc + rule.w * base.getD (Chart.cidx words.size nNT i split rule.r1.toNat) 0 *
                base.getD (Chart.cidx words.size nNT split j rule.r2.toNat) 0
            else acc)
          (chart.getD (Chart.cidx words.size nNT i j a) 0) := by
  induction rules with
  | nil => intro chart base _ _; rfl
  | cons r rs ih =>
    intro chart base hsize hagree
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hguard : IndexedCNF.ruleInBounds nNT r = true
    · obtain ⟨hlhs, hr1, hr2⟩ := ruleInBounds_decompose hguard
      rw [if_pos hguard]
      -- the write leaves every cell of a different span unchanged
      have hpres : ∀ x y b : Nat, x < y → y ≤ words.size → b < nNT → ¬(x = i ∧ y = j) →
          (chart.set! (Chart.cidx words.size nNT i j r.lhs.toNat)
              (chart[Chart.cidx words.size nNT i j r.lhs.toNat]! +
                r.w * chart[Chart.cidx words.size nNT i split r.r1.toNat]! *
                  chart[Chart.cidx words.size nNT split j r.r2.toNat]!)).getD
            (Chart.cidx words.size nNT x y b) 0 =
            chart.getD (Chart.cidx words.size nNT x y b) 0 := by
        intro x y b hxy hyn hb hne
        refine setAdd_getD_ne _ _ _ _ fun heq ↦ ?_
        obtain ⟨hxi, hyj, -⟩ := Chart.cidx_inj hij hjn hxy hyn hlhs hb heq
        exact hne ⟨hxi.symm, hyj.symm⟩
      have hagree' : AgreesOnChildren words nNT i j
          (chart.set! (Chart.cidx words.size nNT i j r.lhs.toNat)
            (chart[Chart.cidx words.size nNT i j r.lhs.toNat]! +
              r.w * chart[Chart.cidx words.size nNT i split r.r1.toNat]! *
                chart[Chart.cidx words.size nNT split j r.r2.toNat]!)) base := by
        intro s b hs hsj hb
        exact ⟨(hpres i s b hs (by omega) hb (by omega)).trans (hagree s b hs hsj hb).1,
          (hpres s j b hsj hjn hb (by omega)).trans (hagree s b hs hsj hb).2⟩
      rw [ih _ base (by rw [Array.size_set!]; exact hsize) hagree']
      -- evaluate the head write on the target cell
      by_cases hlhsa : r.lhs.toNat = a
      · subst hlhsa
        rw [if_pos ⟨hguard, rfl⟩,
          setAdd_getD_self _ _ _ (hsize ▸ Chart.cidx_lt_entryCount hij hjn hlhs),
          getElem_bang_eq_getD _ _ (hsize ▸ Chart.cidx_lt_entryCount hs1 (by omega) hr1),
          getElem_bang_eq_getD _ _ (hsize ▸ Chart.cidx_lt_entryCount hs2 hjn hr2),
          (hagree split r.r1.toNat hs1 hs2 hr1).1, (hagree split r.r2.toNat hs1 hs2 hr2).2]
      · have hcell :
            (chart.set! (Chart.cidx words.size nNT i j r.lhs.toNat)
                (chart[Chart.cidx words.size nNT i j r.lhs.toNat]! +
                  r.w * chart[Chart.cidx words.size nNT i split r.r1.toNat]! *
                    chart[Chart.cidx words.size nNT split j r.r2.toNat]!)).getD
              (Chart.cidx words.size nNT i j a) 0 =
              chart.getD (Chart.cidx words.size nNT i j a) 0 := by
          refine setAdd_getD_ne _ _ _ _ fun heq ↦ ?_
          exact hlhsa (Chart.cidx_inj hij hjn hij hjn hlhs ha heq).2.2
        rw [if_neg fun hand ↦ hlhsa hand.2, hcell]
    · rw [if_neg hguard, if_neg fun hand ↦ hguard hand.1, ih _ base hsize hagree]

private theorem binSplits_getD (splits : List Nat) (grammar : CNF K) (words : Array Tok)
    (i j a : Nat) (hij : i < j) (hjn : j ≤ words.size) (ha : a < grammar.nNT)
    (hmem : ∀ s ∈ splits, i < s ∧ s < j) :
    ∀ chart base : Array K, chart.size = Chart.entryCount words.size grammar.nNT →
      AgreesOnChildren words grammar.nNT i j chart base →
      (splits.foldl (fun chart split ↦ binStep grammar words i j split chart) chart).getD
          (Chart.cidx words.size grammar.nNT i j a) 0 =
        splits.foldl
          (fun acc split ↦
            grammar.bin.toList.foldl
              (fun acc rule ↦
                if IndexedCNF.ruleInBounds grammar.nNT rule = true ∧ rule.lhs.toNat = a then
                  acc + rule.w *
                    base.getD (Chart.cidx words.size grammar.nNT i split rule.r1.toNat) 0 *
                    base.getD (Chart.cidx words.size grammar.nNT split j rule.r2.toNat) 0
                else acc)
              acc)
          (chart.getD (Chart.cidx words.size grammar.nNT i j a) 0) := by
  induction splits with
  | nil => intro chart base _ _; rfl
  | cons s ss ih =>
    intro chart base hsize hagree
    obtain ⟨hs1, hs2⟩ := hmem s List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons]
    have hagree' : AgreesOnChildren words grammar.nNT i j
        (binStep grammar words i j s chart) base := by
      intro t b ht htj hb
      exact ⟨(binStep_getD_ne_span grammar words chart i j s i t b hij hjn ht (by omega) hb
          (by omega)).trans (hagree t b ht htj hb).1,
        (binStep_getD_ne_span grammar words chart i j s t j b hij hjn htj hjn hb
          (by omega)).trans (hagree t b ht htj hb).2⟩
    rw [ih (fun x hx ↦ hmem x (List.mem_cons_of_mem s hx)) _ base
      ((binStep_size grammar words i j s chart).trans hsize) hagree']
    have hhead : (binStep grammar words i j s chart).getD
        (Chart.cidx words.size grammar.nNT i j a) 0 =
        grammar.bin.toList.foldl
          (fun acc rule ↦
            if IndexedCNF.ruleInBounds grammar.nNT rule = true ∧ rule.lhs.toNat = a then
              acc + rule.w *
                base.getD (Chart.cidx words.size grammar.nNT i s rule.r1.toNat) 0 *
                base.getD (Chart.cidx words.size grammar.nNT s j rule.r2.toNat) 0
            else acc)
          (chart.getD (Chart.cidx words.size grammar.nNT i j a) 0) := by
      have hstep : binStep grammar words i j s chart =
          grammar.bin.toList.foldl
            (fun chart rule ↦
              if IndexedCNF.ruleInBounds grammar.nNT rule then
                chart.set! (Chart.cidx words.size grammar.nNT i j rule.lhs.toNat)
                  (chart[Chart.cidx words.size grammar.nNT i j rule.lhs.toNat]! +
                    rule.w * chart[Chart.cidx words.size grammar.nNT i s rule.r1.toNat]! *
                      chart[Chart.cidx words.size grammar.nNT s j rule.r2.toNat]!)
              else chart)
            chart := by
        unfold binStep
        rw [← Array.foldl_toList]
      rw [hstep]
      exact binRules_getD grammar.bin.toList words grammar.nNT i j s a hij hjn ha hs1 hs2 chart
        base hsize hagree
    rw [hhead]

/-- One iteration of a width pass: fill the cells for span `(i, i + width)` over every split. -/
private def binIter (grammar : CNF K) (words : Array Tok) (width : Nat) (chart : Array K)
    (i : Nat) : Array K :=
  (List.range' (i + 1) (i + width - (i + 1))).foldl
    (fun chart split ↦ binStep grammar words i (i + width) split chart) chart

/-- One whole width pass of the CKY sweep. -/
private def widthPass (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (width : Nat) : Array K :=
  (List.range (words.size + 1 - width)).foldl (binIter grammar words width) chart

/-- The chart after the lexical sweep. -/
private def lexPass (grammar : CNF K) (words : Array Tok) : Array K :=
  (List.range words.size).foldl (lexStep grammar words)
    (Array.replicate (Chart.entryCount words.size grammar.nNT) 0)

/-- The chart state just before the width-`w` pass reaches position `i`. -/
private def binPrefix (grammar : CNF K) (words : Array Tok) (w i : Nat) : Array K :=
  (List.range' 0 i).foldl (binIter grammar words w)
    ((List.range' 2 (w - 2)).foldl (widthPass grammar words) (lexPass grammar words))

private theorem binIter_size (grammar : CNF K) (words : Array Tok) (width : Nat)
    (chart : Array K) (i : Nat) : (binIter grammar words width chart i).size = chart.size := by
  unfold binIter
  exact foldl_size_invariant _ _ (fun chart split ↦ binStep_size grammar words i (i + width)
    split chart) chart

private theorem widthPass_size (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (width : Nat) : (widthPass grammar words chart width).size = chart.size := by
  unfold widthPass
  exact foldl_size_invariant _ _ (fun chart i ↦ binIter_size grammar words width chart i) chart

private theorem lexPass_size (grammar : CNF K) (words : Array Tok) :
    (lexPass grammar words).size = Chart.entryCount words.size grammar.nNT := by
  unfold lexPass
  rw [foldl_size_invariant _ _ fun chart p ↦ lexStep_size grammar words chart p]
  exact Array.size_replicate

private theorem binPrefix_size (grammar : CNF K) (words : Array Tok) (w i : Nat) :
    (binPrefix grammar words w i).size = Chart.entryCount words.size grammar.nNT := by
  unfold binPrefix
  rw [foldl_size_invariant _ _ fun chart i' ↦ binIter_size grammar words w chart i',
    foldl_size_invariant _ _ fun chart w' ↦ widthPass_size grammar words chart w']
  exact lexPass_size grammar words

private theorem binIter_getD_ne (grammar : CNF K) (words : Array Tok) (width : Nat)
    (chart : Array K) (i' x y b : Nat) (hw : 0 < width) (hspan : i' + width ≤ words.size)
    (hxy : x < y) (hyn : y ≤ words.size) (hb : b < grammar.nNT)
    (hne : ¬(x = i' ∧ y = i' + width)) :
    (binIter grammar words width chart i').getD (Chart.cidx words.size grammar.nNT x y b) 0 =
      chart.getD (Chart.cidx words.size grammar.nNT x y b) 0 := by
  unfold binIter
  refine foldl_getD_invariant _ _ _ (fun chart split _ ↦ ?_) chart
  exact binStep_getD_ne_span grammar words chart i' (i' + width) split x y b (by omega) hspan
    hxy hyn hb hne

private theorem widthPass_getD_ne (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (width x y b : Nat) (hw : 0 < width) (hxy : x < y) (hyn : y ≤ words.size)
    (hb : b < grammar.nNT) (hne : y - x ≠ width) :
    (widthPass grammar words chart width).getD (Chart.cidx words.size grammar.nNT x y b) 0 =
      chart.getD (Chart.cidx words.size grammar.nNT x y b) 0 := by
  unfold widthPass
  refine foldl_getD_invariant _ _ _ (fun chart i' hi' ↦ ?_) chart
  have hi'lt := List.mem_range.mp hi'
  exact binIter_getD_ne grammar words width chart i' x y b hw (by omega) hxy hyn hb
    (by omega)

private theorem lexPass_getD_wide (grammar : CNF K) (words : Array Tok) (x y b : Nat)
    (hxy : x < y) (hyn : y ≤ words.size) (hb : b < grammar.nNT) (hwide : y - x ≠ 1) :
    (lexPass grammar words).getD (Chart.cidx words.size grammar.nNT x y b) 0 = 0 := by
  unfold lexPass
  rw [foldl_getD_invariant _ _ _ fun chart p hp ↦
    lexStep_getD_ne_span grammar words chart p x y b (List.mem_range.mp hp) hxy hyn hb
      (by omega)]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- The weight the binary layer owes cell `(i, j, a)`: the split/rule accumulation of the
Bellman recurrence, reading children from `chart`. -/
def binCellSum (grammar : CNF K) (words : Array Tok) (chart : Array K) (i j a : Nat) : K :=
  (List.range' (i + 1) (j - (i + 1))).foldl
    (fun acc split ↦
      grammar.bin.toList.foldl
        (fun acc rule ↦
          if IndexedCNF.ruleInBounds grammar.nNT rule = true ∧ rule.lhs.toNat = a then
            acc + rule.w *
              chart.getD (Chart.cidx words.size grammar.nNT i split rule.r1.toNat) 0 *
              chart.getD (Chart.cidx words.size grammar.nNT split j rule.r2.toNat) 0
          else acc)
        acc)
    0

/--
**Binary-layer correctness.**  Every cell of width at least two in the reference chart holds
exactly the split/rule accumulation of the CKY Bellman recurrence, with both children read
from the final chart.  Together with `ckyNaive_getD_lex` this characterizes the whole chart.
No algebraic laws are used, so this holds for every `SemiringOps` carrier.
-/
theorem ckyNaive_getD_bin (grammar : CNF K) (words : Array Tok) (i j a : Nat)
    (hij2 : i + 2 ≤ j) (hjn : j ≤ words.size) (ha : a < grammar.nNT) :
    (ckyNaive grammar words).getD (Chart.cidx words.size grammar.nNT i j a) 0 =
      binCellSum grammar words (ckyNaive grammar words) i j a := by
  obtain ⟨w, rfl⟩ : ∃ w, j = i + w := ⟨j - i, by omega⟩
  have hw2 : 2 ≤ w := by omega
  rw [ckyNaive_eq_fold]
  have hsplitW : List.range' 2 (words.size + 1 - 2) =
      List.range' 2 (w - 2) ++ w :: List.range' (w + 1) (words.size - w) := by
    have h1 : words.size + 1 - 2 = (w - 2) + (1 + (words.size - w)) := by omega
    rw [h1, ← List.range'_append_1 (s := 2) (m := w - 2), show 2 + (w - 2) = w by omega,
      ← List.range'_append_1 (s := w) (m := 1)]
    simp [List.range'_succ]
  have hsplitI : List.range (words.size + 1 - w) =
      List.range' 0 i ++ i :: List.range' (i + 1) (words.size + 1 - w - (i + 1)) := by
    have h1 : words.size + 1 - w = i + (1 + (words.size + 1 - w - (i + 1))) := by omega
    conv => lhs; rw [List.range_eq_range', h1]
    rw [← List.range'_append_1 (s := 0) (m := i), ← List.range'_append_1 (s := 0 + i) (m := 1)]
    simp [List.range'_succ]
  have hFeq : ckyNaiveFold grammar words =
      (List.range' (w + 1) (words.size - w)).foldl (widthPass grammar words)
        ((List.range' (i + 1) (words.size + 1 - w - (i + 1))).foldl (binIter grammar words w)
          (binIter grammar words w (binPrefix grammar words w i) i)) := by
    show (List.range' 2 (words.size + 1 - 2)).foldl (widthPass grammar words)
        (lexPass grammar words) = _
    rw [hsplitW, List.foldl_append, List.foldl_cons]
    show (List.range' (w + 1) (words.size - w)).foldl (widthPass grammar words)
        ((List.range (words.size + 1 - w)).foldl (binIter grammar words w)
          ((List.range' 2 (w - 2)).foldl (widthPass grammar words) (lexPass grammar words))) = _
    rw [hsplitI, List.foldl_append, List.foldl_cons]
    rfl
  have hQsize := binPrefix_size grammar words w i
  have hQzero : (binPrefix grammar words w i).getD
      (Chart.cidx words.size grammar.nNT i (i + w) a) 0 = 0 := by
    have hiters : ∀ (chart : Array K) (i' : Nat), i' ∈ List.range' 0 i →
        (binIter grammar words w chart i').getD
            (Chart.cidx words.size grammar.nNT i (i + w) a) 0 =
          chart.getD (Chart.cidx words.size grammar.nNT i (i + w) a) 0 := by
      intro chart i' hi'
      obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hi'
      exact binIter_getD_ne grammar words w chart _ i (i + w) a (by omega) (by omega)
        (by omega) hjn ha (by omega)
    have hwidths : ∀ (chart : Array K) (w' : Nat), w' ∈ List.range' 2 (w - 2) →
        (widthPass grammar words chart w').getD
            (Chart.cidx words.size grammar.nNT i (i + w) a) 0 =
          chart.getD (Chart.cidx words.size grammar.nNT i (i + w) a) 0 := by
      intro chart w' hw'
      obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hw'
      exact widthPass_getD_ne grammar words chart _ i (i + w) a (by omega) (by omega) hjn ha
        (by omega)
    unfold binPrefix
    rw [foldl_getD_invariant _ _ _ hiters, foldl_getD_invariant _ _ _ hwidths]
    exact lexPass_getD_wide grammar words i (i + w) a (by omega) hjn ha (by omega)
  have hQagree : AgreesOnChildren words grammar.nNT i (i + w) (binPrefix grammar words w i)
      (ckyNaiveFold grammar words) := by
    intro t b ht htw hb
    have hlaterL : ∀ (chart : Array K) (w' : Nat), w' ∈ List.range' (w + 1) (words.size - w) →
        (widthPass grammar words chart w').getD (Chart.cidx words.size grammar.nNT i t b) 0 =
          chart.getD (Chart.cidx words.size grammar.nNT i t b) 0 := by
      intro chart w' hw'
      obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hw'
      exact widthPass_getD_ne grammar words chart _ i t b (by omega) ht (by omega) hb
        (by omega)
    have hlaterR : ∀ (chart : Array K) (w' : Nat), w' ∈ List.range' (w + 1) (words.size - w) →
        (widthPass grammar words chart w').getD
            (Chart.cidx words.size grammar.nNT t (i + w) b) 0 =
          chart.getD (Chart.cidx words.size grammar.nNT t (i + w) b) 0 := by
      intro chart w' hw'
      obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hw'
      exact widthPass_getD_ne grammar words chart _ t (i + w) b (by omega) htw hjn hb
        (by omega)
    have hitersL : ∀ (chart : Array K) (i' : Nat),
        i' ∈ List.range' (i + 1) (words.size + 1 - w - (i + 1)) →
        (binIter grammar words w chart i').getD (Chart.cidx words.size grammar.nNT i t b) 0 =
          chart.getD (Chart.cidx words.size grammar.nNT i t b) 0 := by
      intro chart i' hi'
      obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hi'
      exact binIter_getD_ne grammar words w chart _ i t b (by omega) (by omega) ht (by omega)
        hb (by omega)
    have hitersR : ∀ (chart : Array K) (i' : Nat),
        i' ∈ List.range' (i + 1) (words.size + 1 - w - (i + 1)) →
        (binIter grammar words w chart i').getD
            (Chart.cidx words.size grammar.nNT t (i + w) b) 0 =
          chart.getD (Chart.cidx words.size grammar.nNT t (i + w) b) 0 := by
      intro chart i' hi'
      obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hi'
      exact binIter_getD_ne grammar words w chart _ t (i + w) b (by omega) (by omega) htw hjn
        hb (by omega)
    constructor
    · rw [hFeq, foldl_getD_invariant _ _ _ hlaterL, foldl_getD_invariant _ _ _ hitersL,
        binIter_getD_ne grammar words w _ i i t b (by omega) hjn ht (by omega) hb (by omega)]
    · rw [hFeq, foldl_getD_invariant _ _ _ hlaterR, foldl_getD_invariant _ _ _ hitersR,
        binIter_getD_ne grammar words w _ i t (i + w) b (by omega) hjn (by omega) hjn hb
          (by omega)]
  have hRval : (binIter grammar words w (binPrefix grammar words w i) i).getD
      (Chart.cidx words.size grammar.nNT i (i + w) a) 0 =
      binCellSum grammar words (ckyNaiveFold grammar words) i (i + w) a := by
    show ((List.range' (i + 1) (i + w - (i + 1))).foldl
        (fun chart split ↦ binStep grammar words i (i + w) split chart)
        (binPrefix grammar words w i)).getD (Chart.cidx words.size grammar.nNT i (i + w) a) 0 =
      _
    rw [binSplits_getD (List.range' (i + 1) (i + w - (i + 1))) grammar words i (i + w) a
        (by omega) hjn ha
        (fun s hs ↦ by
          obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hs
          exact ⟨by omega, by omega⟩)
        (binPrefix grammar words w i) (ckyNaiveFold grammar words) hQsize hQagree, hQzero]
    rfl
  have hlater : ∀ (chart : Array K) (w' : Nat), w' ∈ List.range' (w + 1) (words.size - w) →
      (widthPass grammar words chart w').getD
          (Chart.cidx words.size grammar.nNT i (i + w) a) 0 =
        chart.getD (Chart.cidx words.size grammar.nNT i (i + w) a) 0 := by
    intro chart w' hw'
    obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hw'
    exact widthPass_getD_ne grammar words chart _ i (i + w) a (by omega) (by omega) hjn ha
      (by omega)
  have hafter : ∀ (chart : Array K) (i' : Nat),
      i' ∈ List.range' (i + 1) (words.size + 1 - w - (i + 1)) →
      (binIter grammar words w chart i').getD
          (Chart.cidx words.size grammar.nNT i (i + w) a) 0 =
        chart.getD (Chart.cidx words.size grammar.nNT i (i + w) a) 0 := by
    intro chart i' hi'
    obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp hi'
    exact binIter_getD_ne grammar words w chart _ i (i + w) a (by omega) (by omega) (by omega)
      hjn ha (by omega)
  conv => lhs; rw [hFeq]
  rw [foldl_getD_invariant _ _ _ hlater, foldl_getD_invariant _ _ _ hafter, hRval]

end Nlp.Parse
