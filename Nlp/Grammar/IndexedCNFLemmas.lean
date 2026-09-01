import Nlp.Grammar.IndexedCNF

/-!
# Structural lemmas for the CNF pair index

`IndexedCNF.ofCNF` is a two-pass counting sort written with `Id.run`, `for` loops, and mutable
arrays.  Following the project cookbook (`Nlp.Sequence.ChainLemmas`,
`Nlp.Core.Engine.InsideLemmas`), this module first refines the kernel into three plain folds
(`ofCNF_eq_fold`), then proves the structural facts of obligation IDX-1a
needed by every indexed lookup:

* `pairStart_size` — the boundary table has one slot per pair key plus a terminator;
* `pairStart_getD` — slot `key` holds the prefix sum of the first `key + 1` bucket counters;
* `pairStart_monotone` — boundaries never decrease, so every bucket interval
  `[pairStart[key], pairStart[key + 1])` is well formed;
* `binSorted_size` / `binSource_size` — the rule store ends exactly at the last boundary, so
  every bucket interval is in bounds (`pairStart_getD_le_binSorted_size`);
* `pairStart_getD_zero` — the first bucket starts at slot zero.

No algebraic laws are involved anywhere: this is loop bookkeeping only.
-/

namespace Nlp

namespace IndexedCNF

variable {K : Type}

/-! ## Functional restatement of the three passes -/

/-- Pass 1, one step: bump the counter one past the rule's pair key (in-bounds rules only). -/
def countStep (nNT : Nat) (counts : Array Nat) (rule : BinRule K) : Array Nat :=
  if ruleInBounds nNT rule then
    counts.modify (pairKey nNT rule.r1.toNat rule.r2.toNat + 1) (fun count ↦ count + 1)
  else counts

/-- Pass 1: bucket counters.  Slot `key + 1` counts the in-bounds rules with pair key `key`;
slot `0` stays zero. -/
def bucketCounts (grammar : CNF K) : Array Nat :=
  grammar.bin.foldl (countStep grammar.nNT) (Array.replicate (grammar.nNT * grammar.nNT + 1) 0)

/-- Sum of the first `m` bucket counters: where bucket `m` starts in the sorted rule store. -/
def prefixTotal (grammar : CNF K) : Nat → Nat
  | 0 => 0
  | m + 1 => prefixTotal grammar m + (bucketCounts grammar)[m]!

/-- Pass 2, one step: extend the running total by bucket `key` and record it. -/
def scanStep (counts : Array Nat) (state : Array Nat × Nat) (key : Nat) : Array Nat × Nat :=
  (state.1.set! key (state.2 + counts[key]!), state.2 + counts[key]!)

/-- Pass 2 over the first `m` keys: the boundary table under construction, with the running
total of counted rules. -/
def prefixScan (grammar : CNF K) (m : Nat) : Array Nat × Nat :=
  (List.range m).foldl (scanStep (bucketCounts grammar))
    (Array.replicate (grammar.nNT * grammar.nNT + 1) 0, 0)

/-- Functional form of the `pairStart` field. -/
def pairStartFun (grammar : CNF K) : Array Nat :=
  (prefixScan grammar (grammar.nNT * grammar.nNT + 1)).1

/-- Functional form of the total number of bucketed rules. -/
def totalFun (grammar : CNF K) : Nat :=
  (prefixScan grammar (grammar.nNT * grammar.nNT + 1)).2

/-- Pass 3, one step: place rule `sourceIndex` at its bucket's fill pointer and advance the
pointer.  State: fill pointers, sorted rules, source indices. -/
def fillStep [Inhabited K] (grammar : CNF K)
    (state : Array Nat × Array (BinRule K) × Array Nat) (sourceIndex : Nat) :
    Array Nat × Array (BinRule K) × Array Nat :=
  if ruleInBounds grammar.nNT grammar.bin[sourceIndex]! then
    let rule := grammar.bin[sourceIndex]!
    let key := pairKey grammar.nNT rule.r1.toNat rule.r2.toNat
    (state.1.set! key (state.1[key]! + 1),
      state.2.1.set! state.1[key]! rule,
      state.2.2.set! state.1[key]! sourceIndex)
  else state

/-- Pass 3: scatter every in-bounds rule into its bucket, in source order. -/
def fillRun [Inhabited K] (grammar : CNF K) : Array Nat × Array (BinRule K) × Array Nat :=
  (List.range grammar.bin.size).foldl (fillStep grammar)
    (pairStartFun grammar, Array.replicate (totalFun grammar) default,
      Array.replicate (totalFun grammar) 0)

/-! ## Kernel refinement -/

private theorem id_pure_eq {α : Type v} (a : α) : (pure a : Id α) = a := rfl

private theorem id_bind_eq {α β : Type v} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

private theorem id_forIn_yield_eq_foldl {α : Type v} {β : Type w} (l : List α) (f : α → β → β)
    (init : β) :
    (forIn (m := Id) l init fun a b ↦ ForInStep.yield (f a b)) =
      l.foldl (fun b a ↦ f a b) init :=
  List.forIn_pure_yield_eq_foldl f init

private theorem id_forIn_ite_yield_eq_foldl {α : Type v} {β : Type w} (xs : Array α)
    (c : α → Bool) (f : α → β → β) (init : β) :
    (forIn (m := Id) xs init fun a b ↦
        if c a = true then ForInStep.yield (f a b) else ForInStep.yield b) =
      xs.foldl (fun b a ↦ if c a = true then f a b else b) init := by
  have h : (fun (a : α) (b : β) ↦
      (if c a = true then ForInStep.yield (f a b) else ForInStep.yield b : Id (ForInStep β))) =
      fun a b ↦ ForInStep.yield (if c a = true then f a b else b) := by
    funext a b
    split <;> rfl
  rw [h]
  exact Array.forIn_pure_yield_eq_foldl _ init

private theorem id_forIn_ite_yield_eq_foldl_list {α : Type v} {β : Type w} (l : List α)
    (c : α → Bool) (f : α → β → β) (init : β) :
    (forIn (m := Id) l init fun a b ↦
        if c a = true then ForInStep.yield (f a b) else ForInStep.yield b) =
      l.foldl (fun b a ↦ if c a = true then f a b else b) init := by
  have h : (fun (a : α) (b : β) ↦
      (if c a = true then ForInStep.yield (f a b) else ForInStep.yield b : Id (ForInStep β))) =
      fun a b ↦ ForInStep.yield (if c a = true then f a b else b) := by
    funext a b
    split <;> rfl
  rw [h]
  exact List.forIn_pure_yield_eq_foldl _ init

/-- **Kernel refinement.**  The imperative counting sort is the composition of the three
functional passes.  No algebraic laws are used: this is loop bookkeeping only. -/
theorem ofCNF_eq_fold [Inhabited K] (grammar : CNF K) :
    ofCNF grammar =
      ⟨grammar, (fillRun grammar).2.1, (fillRun grammar).2.2, pairStartFun grammar⟩ := by
  unfold ofCNF
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', id_bind_eq, id_pure_eq,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range', id_forIn_yield_eq_foldl, id_forIn_ite_yield_eq_foldl,
    id_forIn_ite_yield_eq_foldl_list]
  rfl

/-! ## Pass 1: the zero slot is never touched -/

private theorem foldl_countStep_getElem?_zero (nNT : Nat) (rules : List (BinRule K))
    (counts : Array Nat) :
    (rules.foldl (countStep nNT) counts)[0]? = counts[0]? := by
  induction rules generalizing counts with
  | nil => rfl
  | cons rule rules ih =>
    rw [List.foldl_cons, ih]
    unfold countStep
    split
    · rw [Array.getElem?_modify]
      simp
    · rfl

private theorem bucketCounts_getElem?_zero (grammar : CNF K) :
    (bucketCounts grammar)[0]? = some 0 := by
  unfold bucketCounts
  rw [← Array.foldl_toList, foldl_countStep_getElem?_zero]
  simp

/-! ## Pass 2: sizes, prefix sums, monotonicity -/

private theorem scanStep_fst_size (counts : Array Nat) (state : Array Nat × Nat) (key : Nat) :
    (scanStep counts state key).1.size = state.1.size := by
  show (state.1.set! key (state.2 + counts[key]!)).size = state.1.size
  exact Array.size_set! _ _ _

private theorem scanStep_snd (counts : Array Nat) (state : Array Nat × Nat) (key : Nat) :
    (scanStep counts state key).2 = state.2 + counts[key]! := rfl

private theorem scanStep_fst_getD_ne (counts : Array Nat) (state : Array Nat × Nat)
    {key k : Nat} (h : key ≠ k) :
    (scanStep counts state key).1.getD k 0 = state.1.getD k 0 := by
  show (state.1.set! key (state.2 + counts[key]!)).getD k 0 = state.1.getD k 0
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne h, ← Array.getD_eq_getD_getElem?]

private theorem scanStep_fst_getD_self (counts : Array Nat) (state : Array Nat × Nat)
    {key : Nat} (h : key < state.1.size) :
    (scanStep counts state key).1.getD key 0 = state.2 + counts[key]! := by
  show (state.1.set! key (state.2 + counts[key]!)).getD key 0 = state.2 + counts[key]!
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h]
  rfl

private theorem prefixScan_succ (grammar : CNF K) (m : Nat) :
    prefixScan grammar (m + 1) = scanStep (bucketCounts grammar) (prefixScan grammar m) m := by
  unfold prefixScan
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem prefixScan_fst_size (grammar : CNF K) (m : Nat) :
    (prefixScan grammar m).1.size = grammar.nNT * grammar.nNT + 1 := by
  induction m with
  | zero => exact Array.size_replicate
  | succ m ih =>
    rw [prefixScan_succ, scanStep_fst_size]
    exact ih

private theorem prefixScan_snd (grammar : CNF K) (m : Nat) :
    (prefixScan grammar m).2 = prefixTotal grammar m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [prefixScan_succ, scanStep_snd, ih, prefixTotal]

private theorem prefixScan_fst_getD (grammar : CNF K) :
    ∀ m k : Nat, k < m → m ≤ grammar.nNT * grammar.nNT + 1 →
      (prefixScan grammar m).1.getD k 0 = prefixTotal grammar (k + 1)
  | 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | m + 1, k, hk, hm => by
    rw [prefixScan_succ]
    by_cases hkm : k = m
    · subst hkm
      rw [scanStep_fst_getD_self _ _ (by rw [prefixScan_fst_size]; omega), prefixScan_snd,
        prefixTotal]
    · rw [scanStep_fst_getD_ne _ _ (by omega : m ≠ k)]
      exact prefixScan_fst_getD grammar m k (by omega) (by omega)

private theorem prefixTotal_mono (grammar : CNF K) {m n : Nat} (h : m ≤ n) :
    prefixTotal grammar m ≤ prefixTotal grammar n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    simp only [prefixTotal]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

private theorem pairStartFun_getD_last (grammar : CNF K) :
    (pairStartFun grammar).getD (grammar.nNT * grammar.nNT) 0 = totalFun grammar := by
  unfold pairStartFun totalFun
  rw [prefixScan_fst_getD grammar (grammar.nNT * grammar.nNT + 1) (grammar.nNT * grammar.nNT)
      (Nat.lt_succ_self _) (Nat.le_refl _), prefixScan_snd]

/-! ## Pass 3: only writes into the preallocated stores -/

private theorem fillStep_binSorted_size [Inhabited K] (grammar : CNF K)
    (state : Array Nat × Array (BinRule K) × Array Nat) (sourceIndex : Nat) :
    (fillStep grammar state sourceIndex).2.1.size = state.2.1.size := by
  unfold fillStep
  split
  · simp
  · rfl

private theorem fillStep_binSource_size [Inhabited K] (grammar : CNF K)
    (state : Array Nat × Array (BinRule K) × Array Nat) (sourceIndex : Nat) :
    (fillStep grammar state sourceIndex).2.2.size = state.2.2.size := by
  unfold fillStep
  split
  · simp
  · rfl

private theorem foldl_fillStep_binSorted_size [Inhabited K] (grammar : CNF K)
    (indices : List Nat) (state : Array Nat × Array (BinRule K) × Array Nat) :
    (indices.foldl (fillStep grammar) state).2.1.size = state.2.1.size := by
  induction indices generalizing state with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons, ih, fillStep_binSorted_size]

private theorem foldl_fillStep_binSource_size [Inhabited K] (grammar : CNF K)
    (indices : List Nat) (state : Array Nat × Array (BinRule K) × Array Nat) :
    (indices.foldl (fillStep grammar) state).2.2.size = state.2.2.size := by
  induction indices generalizing state with
  | nil => rfl
  | cons i is ih => rw [List.foldl_cons, ih, fillStep_binSource_size]

private theorem fillRun_binSorted_size [Inhabited K] (grammar : CNF K) :
    (fillRun grammar).2.1.size = totalFun grammar := by
  unfold fillRun
  rw [foldl_fillStep_binSorted_size]
  exact Array.size_replicate

private theorem fillRun_binSource_size [Inhabited K] (grammar : CNF K) :
    (fillRun grammar).2.2.size = totalFun grammar := by
  unfold fillRun
  rw [foldl_fillStep_binSource_size]
  exact Array.size_replicate

/-! ## Structural facts about `ofCNF` (IDX-1a) -/

/-- The boundary table has one slot per pair key, plus the terminating total. -/
theorem pairStart_size [Inhabited K] (grammar : CNF K) :
    (ofCNF grammar).pairStart.size = grammar.nNT * grammar.nNT + 1 := by
  rw [ofCNF_eq_fold]
  exact prefixScan_fst_size grammar _

/-- Boundary characterization: slot `key` holds the prefix sum of the first `key + 1` bucket
counters. -/
theorem pairStart_getD [Inhabited K] (grammar : CNF K) {key : Nat}
    (hkey : key ≤ grammar.nNT * grammar.nNT) :
    (ofCNF grammar).pairStart.getD key 0 = prefixTotal grammar (key + 1) := by
  rw [ofCNF_eq_fold]
  exact prefixScan_fst_getD grammar _ key (by omega) (Nat.le_refl _)

/-- Bucket boundaries never decrease. -/
theorem pairStart_monotone [Inhabited K] (grammar : CNF K) {k l : Nat} (hkl : k ≤ l)
    (hl : l ≤ grammar.nNT * grammar.nNT) :
    (ofCNF grammar).pairStart.getD k 0 ≤ (ofCNF grammar).pairStart.getD l 0 := by
  rw [pairStart_getD grammar (Nat.le_trans hkl hl), pairStart_getD grammar hl]
  exact prefixTotal_mono grammar (Nat.succ_le_succ hkl)

/-- Bucket `key`'s interval is well formed: its start does not pass its end. -/
theorem pairStart_le_succ [Inhabited K] (grammar : CNF K) {key : Nat}
    (hkey : key < grammar.nNT * grammar.nNT) :
    (ofCNF grammar).pairStart.getD key 0 ≤ (ofCNF grammar).pairStart.getD (key + 1) 0 :=
  pairStart_monotone grammar (Nat.le_succ key) hkey

/-- Pass 1 never touches counter slot `0`, so the first bucket starts at slot zero. -/
theorem pairStart_getD_zero [Inhabited K] (grammar : CNF K) :
    (ofCNF grammar).pairStart.getD 0 0 = 0 := by
  rw [pairStart_getD grammar (Nat.zero_le _)]
  show prefixTotal grammar 0 + (bucketCounts grammar)[0]! = 0
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, bucketCounts_getElem?_zero]
  rfl

/-- The sorted rule store ends exactly at the last boundary: total = last prefix sum. -/
theorem binSorted_size [Inhabited K] (grammar : CNF K) :
    (ofCNF grammar).binSorted.size =
      (ofCNF grammar).pairStart.getD (grammar.nNT * grammar.nNT) 0 := by
  rw [ofCNF_eq_fold]
  exact (fillRun_binSorted_size grammar).trans (pairStartFun_getD_last grammar).symm

/-- The parallel source-index store has exactly one entry per sorted rule. -/
theorem binSource_size [Inhabited K] (grammar : CNF K) :
    (ofCNF grammar).binSource.size = (ofCNF grammar).binSorted.size := by
  rw [ofCNF_eq_fold]
  exact (fillRun_binSource_size grammar).trans (fillRun_binSorted_size grammar).symm

/-- Every boundary is bounded by the store size: bucket intervals lie within `binSorted`. -/
theorem pairStart_getD_le_binSorted_size [Inhabited K] (grammar : CNF K) {key : Nat}
    (hkey : key ≤ grammar.nNT * grammar.nNT) :
    (ofCNF grammar).pairStart.getD key 0 ≤ (ofCNF grammar).binSorted.size := by
  rw [binSorted_size]
  exact pairStart_monotone grammar hkey (Nat.le_refl _)

/-! ## `getElem!` forms -/

/-- `pairStart_getD` in `getElem!` form. -/
theorem pairStart_getElem! [Inhabited K] (grammar : CNF K) {key : Nat}
    (hkey : key ≤ grammar.nNT * grammar.nNT) :
    (ofCNF grammar).pairStart[key]! = prefixTotal grammar (key + 1) := by
  rw [Array.getElem!_eq_getD]
  exact pairStart_getD grammar hkey

/-- `pairStart_monotone` in `getElem!` form. -/
theorem pairStart_monotone_getElem! [Inhabited K] (grammar : CNF K) {k l : Nat} (hkl : k ≤ l)
    (hl : l ≤ grammar.nNT * grammar.nNT) :
    (ofCNF grammar).pairStart[k]! ≤ (ofCNF grammar).pairStart[l]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  exact pairStart_monotone grammar hkl hl

/-- `binSorted_size` in `getElem!` form: the store ends exactly at the last boundary. -/
theorem binSorted_size_getElem! [Inhabited K] (grammar : CNF K) :
    (ofCNF grammar).binSorted.size = (ofCNF grammar).pairStart[grammar.nNT * grammar.nNT]! := by
  rw [Array.getElem!_eq_getD]
  exact binSorted_size grammar

end IndexedCNF

end Nlp
