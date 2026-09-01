import Nlp.Parse.OneBest

/-!
# Value-chart refinement for one-best CKY

`ckyOneBest` mirrors `ckyNaive`'s loop structure while additionally threading a backpointer
array.  This module proves the oracle equation that the tests assert with `native_decide`
for the value-chart refinement: the first component of `ckyOneBest` is
*exactly* `ckyNaive`'s chart, for every carrier and every `better` predicate.  No algebraic
laws are used — the backpointer array is write-only with respect to the value chart, so the
proof is pure loop bookkeeping.

The route is the project's de-imperativization cookbook (`Nlp/Sequence/ChainLemmas.lean`,
`Nlp/Core/Engine/InsideLemmas.lean`): normalize both `Id.run do` kernels to nested
`List.foldl`/`Array.foldl` (`ite_yield_eq` additionally pulls `ForInStep.yield` out of the
conditional loop bodies), then collapse the paired `(chart, back)` state with
`foldl_pair_fst` — a fold whose first component never reads the second projects onto a fold
over first components alone — once per loop level.  `foldl_range_size` bridges the two
iteration styles (`ckyOneBest` walks rule *indices*, `ckyNaive` walks rule *values*).
-/

namespace Nlp.Parse

variable {K : Type} [SemiringOps K] [Inhabited K]

/-! ## Functional form of the `ckyNaive` sweep

One definition per loop level, innermost first.  These spell out exactly the step functions
that the cookbook normalization extracts from `ckyNaive`; the final `refine` steps of the main
proof identify them definitionally.
-/

/-- One lexical rule folded into the value chart: `ckyNaive`'s innermost lexical body. -/
private def lexRuleStep (grammar : CNF K) (words : Array Tok) (i : Nat)
    (chart : Array K) (rule : LexRule K) : Array K :=
  if (rule.tok == words[i]! && decide (rule.lhs.toNat < grammar.nNT)) = true then
    chart.set! (Chart.cidx words.size grammar.nNT i (i + 1) rule.lhs.toNat)
      (chart[Chart.cidx words.size grammar.nNT i (i + 1) rule.lhs.toNat]! + rule.w)
  else chart

/-- All lexical rules folded into the chart at sentence position `i`. -/
private def lexLineStep (grammar : CNF K) (words : Array Tok) (chart : Array K) (i : Nat) :
    Array K :=
  grammar.lex.foldl (lexRuleStep grammar words i) chart

/-- One binary rule folded into the chart for span `[i, i + width)` split at `split`. -/
private def binRuleStep (grammar : CNF K) (words : Array Tok) (width i split : Nat)
    (chart : Array K) (rule : BinRule K) : Array K :=
  if IndexedCNF.ruleInBounds grammar.nNT rule = true then
    chart.set! (Chart.cidx words.size grammar.nNT i (i + width) rule.lhs.toNat)
      (chart[Chart.cidx words.size grammar.nNT i (i + width) rule.lhs.toNat]! +
        rule.w * chart[Chart.cidx words.size grammar.nNT i split rule.r1.toNat]! *
          chart[Chart.cidx words.size grammar.nNT split (i + width) rule.r2.toNat]!)
  else chart

/-- All binary rules folded in at one split point. -/
private def binSplitStep (grammar : CNF K) (words : Array Tok) (width i : Nat)
    (chart : Array K) (split : Nat) : Array K :=
  grammar.bin.foldl (binRuleStep grammar words width i split) chart

/-- All split points folded in for the span `[i, i + width)`. -/
private def binCellStep (grammar : CNF K) (words : Array Tok) (width : Nat)
    (chart : Array K) (i : Nat) : Array K :=
  List.foldl (binSplitStep grammar words width i) chart
    (List.range' (i + 1) (i + width - (i + 1)))

/-- All spans of one width folded in. -/
private def binWidthStep (grammar : CNF K) (words : Array Tok) (chart : Array K)
    (width : Nat) : Array K :=
  List.foldl (binCellStep grammar words width) chart (List.range (words.size + 1 - width))

/-! ## Cookbook normalizers -/

private theorem id_pure_eq {α : Type v} (a : α) : (pure a : Id α) = a := rfl

private theorem id_bind_eq {α β : Type v} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

private theorem id_forIn_yield_eq_foldl {α : Type v} {β : Type w} (l : List α) (f : α → β → β)
    (init : β) :
    (forIn (m := Id) l init fun a b ↦ ForInStep.yield (f a b)) =
      l.foldl (fun b a ↦ f a b) init :=
  List.forIn_pure_yield_eq_foldl f init

private theorem id_forIn_yield_eq_foldl_arr {α : Type v} {β : Type w} (xs : Array α)
    (f : α → β → β) (init : β) :
    (forIn (m := Id) xs init fun a b ↦ ForInStep.yield (f a b)) =
      xs.foldl (fun b a ↦ f a b) init :=
  Array.forIn_pure_yield_eq_foldl f init

/-- A loop body that yields in both branches of an `if` is a pure-yield body.  Stated over
`Id (ForInStep β)` — the type at which the do-elaborator emits the conditional — so that
`simp` can find it. -/
private theorem ite_yield_eq {c : Prop} [Decidable c] {β : Type v} (x y : β) :
    (if c then ForInStep.yield x else ForInStep.yield y : Id (ForInStep β)) =
      ForInStep.yield (if c then x else y) := by
  split <;> rfl

/-! ## Pair-state collapse -/

/-- A fold over paired state whose first component evolves independently of the second
projects onto the fold of first components. -/
private theorem foldl_pair_fst {α : Type u} {β : Type v} {γ : Type w}
    {l : List γ} {g : α × β → γ → α × β} (f : α → γ → α)
    (h : ∀ (chart : α) (back : β) (c : γ), (g (chart, back) c).fst = f chart c) :
    ∀ (chart : α) (back : β), (l.foldl g (chart, back)).fst = l.foldl f chart := by
  induction l with
  | nil => intro chart back; rfl
  | cons c cs ih =>
    intro chart back
    rw [List.foldl_cons, List.foldl_cons, ← h chart back c]
    exact ih (g (chart, back) c).fst (g (chart, back) c).snd

/-- Folds with the same step function agree when started from equal states. -/
private theorem foldl_congr_init {α : Type u} {β : Type v} {l : List β} {f : α → β → α}
    {a b : α} (h : a = b) : l.foldl f a = l.foldl f b := by
  rw [h]

/-! ## Index iteration versus element iteration -/

/-- Folding a list by positions read back with `getElem!` is folding the list itself. -/
private theorem foldl_getElem_bang {α : Type u} {β : Type v} [Inhabited α] (l : List α)
    (f : β → α → β) :
    ∀ init : β, (List.range l.length).foldl (fun b i ↦ f b l[i]!) init = l.foldl f init := by
  induction l with
  | nil => intro init; rfl
  | cons a as ih =>
    intro init
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.succ_eq_add_one, List.getElem!_cons_zero, List.getElem!_cons_succ]
    exact ih (f init a)

/-- `ckyOneBest` walks rule indices where `ckyNaive` walks rule values; the folds agree. -/
private theorem foldl_range_size {α : Type u} {β : Type v} [Inhabited α] (xs : Array α)
    (f : β → α → β) (init : β) :
    (List.range xs.size).foldl (fun b i ↦ f b xs[i]!) init = xs.foldl f init := by
  have h := foldl_getElem_bang xs.toList f init
  simp only [Array.getElem!_toList, Array.foldl_toList, Array.length_toList] at h
  exact h

/-! ## The oracle equation -/

/--
**Value-chart refinement (VIT-1).**  The one-best kernel's value chart is exactly the
reference CKY chart: the `Back` array is write-only with respect to the chart, and the chart
updates are `ckyNaive`'s verbatim.  Law-free — it holds for every carrier and every `better`.
-/
theorem ckyOneBest_fst (better : K → K → Bool) (grammar : CNF K) (words : Array Tok) :
    (ckyOneBest better grammar words).1 = ckyNaive grammar words := by
  unfold ckyOneBest ckyNaive
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', id_bind_eq, id_pure_eq,
    ite_yield_eq, id_forIn_yield_eq_foldl, id_forIn_yield_eq_foldl_arr, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  refine (foldl_pair_fst (binWidthStep grammar words) ?hbin _ _).trans
    (foldl_congr_init ?hlex)
  case hbin =>
    intro chart back width
    dsimp only [binWidthStep]
    refine foldl_pair_fst (binCellStep grammar words width) ?_ chart back
    intro chart back i
    dsimp only [binCellStep]
    refine foldl_pair_fst (binSplitStep grammar words width i) ?_ chart back
    intro chart back split
    dsimp only [binSplitStep]
    refine (foldl_pair_fst
        (fun b r ↦ binRuleStep grammar words width i split b grammar.bin[r]!) ?_
        chart back).trans
      (foldl_range_size grammar.bin (binRuleStep grammar words width i split) chart)
    intro chart back r
    dsimp only [binRuleStep]
    split
    · split <;> rfl
    · rfl
  case hlex =>
    refine foldl_pair_fst (lexLineStep grammar words) ?_ _ _
    intro chart back i
    dsimp only [lexLineStep]
    refine (foldl_pair_fst (fun b r ↦ lexRuleStep grammar words i b grammar.lex[r]!) ?_
        chart back).trans
      (foldl_range_size grammar.lex (lexRuleStep grammar words i) chart)
    intro chart back r
    dsimp only [lexRuleStep]
    split
    · split <;> rfl
    · rfl

/-- The goal values agree as well: the one-best chart read at the goal cell is
`ckyNaiveGoal`. -/
theorem ckyOneBest_fst_goal (better : K → K → Bool) (grammar : CNF K) (words : Array Tok) :
    (ckyOneBest better grammar words).1.getD (goalIndex grammar words.size) 0 =
      ckyNaiveGoal grammar words := by
  rw [ckyOneBest_fst]
  rfl

end Nlp.Parse
