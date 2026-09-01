import Nlp.Core.Algebra.BigOps
import Nlp.Sequence.Chain

/-!
# Forward-recurrence correctness for linear chains

`Chain.spec` sums the left-folded weight of every state sequence — exponentially many terms.
This module proves the classic collapse: the polynomial forward recurrence (`Chain.forwardFrom`,
a functional restatement of the sweep inside `Chain.forward`) computes the same value, for
*every* carrier satisfying `LawfulChainDP`.  Because `LawfulChainDP` omits multiplication
associativity and left distributivity, the theorem covers genuinely non-associative scoring
carriers; the only algebra used is commutative-monoid addition, right distribution, `1 * a = a`,
and `0 * a = 0`.

The proof is the textbook exchange argument, made precise:

* `visit_add`/`visit_zero` — the suffix evaluator of `spec` is additive in its accumulated path
  weight (this is exactly right distributivity, propagated through the recursion);
* `sumTo_visit_run` — summing the evaluator over the current states equals running the collapsed
  recurrence, by downward induction on the remaining positions, using Fubini (`sumTo_swap`) and
  additivity to merge all prefixes ending in the same state.

The imperative kernel is then refined against the functional recurrence
(`forward_eq_forwardFun`): the `for`/`Array` loops normalize to `List.foldl` over index ranges,
and a loop-invariant induction identifies the mutable score array with the abstract state
vector.  That step is pure bookkeeping — it needs no algebraic laws at all.  The two halves
compose into the end-to-end contract `forward_eq_spec`.
-/

namespace Nlp

namespace Chain

universe u

variable {K : Type u} [SemiringOps K]

/-- One step of the collapsed forward recurrence: merge every predecessor into each next state. -/
def stepVec (chain : Chain K) (t : Nat) (v : Nat → K) : Nat → K :=
  fun next ↦ sumTo chain.nS fun prior ↦ v prior * chain.arc t prior next

/-- Run the collapsed forward recurrence from `position` with accumulated state vector `v`. -/
def forwardFrom (chain : Chain K) (position : Nat) (v : Nat → K) : K :=
  if _h : position ≥ chain.len then sumTo chain.nS fun s ↦ v s * chain.fin s
  else forwardFrom chain (position + 1) (stepVec chain position v)
  termination_by chain.len - position
  decreasing_by omega

/-- The functional forward value: the collapsed recurrence started at the initial vector. -/
def forwardFun (chain : Chain K) : K := forwardFrom chain 1 chain.init

/-- Unfold `spec.visit` past the end of the chain. -/
private theorem visit_of_ge (chain : Chain K) {position : Nat} (prev : Nat) (pw : K)
    (h : position ≥ chain.len) : spec.visit chain position prev pw = pw * chain.fin prev := by
  rw [spec.visit]
  simp [h]

/-- Unfold one interior step of `spec.visit` into a `sumTo` over successor states. -/
private theorem visit_of_lt (chain : Chain K) {position : Nat} (prev : Nat) (pw : K)
    (h : position < chain.len) :
    spec.visit chain position prev pw =
      sumTo chain.nS
        (fun next ↦ spec.visit chain (position + 1) next (pw * chain.arc position prev next)) := by
  rw [spec.visit]
  simp [Nat.not_le_of_lt h]
  rfl

/-- Unfold `forwardFrom` past the end of the chain. -/
theorem forwardFrom_of_ge (chain : Chain K) (position : Nat) (v : Nat → K)
    (h : position ≥ chain.len) :
    forwardFrom chain position v = sumTo chain.nS fun s ↦ v s * chain.fin s := by
  rw [forwardFrom.eq_def, dif_pos h]

/-- Unfold one interior step of `forwardFrom`. -/
theorem forwardFrom_of_lt (chain : Chain K) (position : Nat) (v : Nat → K)
    (h : position < chain.len) :
    forwardFrom chain position v = forwardFrom chain (position + 1) (stepVec chain position v) := by
  rw [forwardFrom.eq_def, dif_neg (by omega : ¬position ≥ chain.len)]

/-- `forwardFrom` only reads its state vector at the live states `0, …, nS - 1`. -/
theorem forwardFrom_congr (chain : Chain K) :
    ∀ (fuel position : Nat) (v w : Nat → K), chain.len - position = fuel →
      (∀ s, s < chain.nS → v s = w s) →
      forwardFrom chain position v = forwardFrom chain position w
  | 0, position, v, w, hfuel, hvw => by
    rw [forwardFrom_of_ge chain position v (by omega),
      forwardFrom_of_ge chain position w (by omega)]
    exact sumTo_congr fun s hs ↦ by rw [hvw s hs]
  | fuel + 1, position, v, w, hfuel, hvw => by
    rw [forwardFrom_of_lt chain position v (by omega),
      forwardFrom_of_lt chain position w (by omega)]
    exact forwardFrom_congr chain fuel (position + 1) _ _ (by omega) fun s _ ↦
      sumTo_congr fun p hp ↦ by rw [hvw p hp]

/-! ## Refining the imperative kernel

The next block proves `Chain.forward = Chain.forwardFun` with no algebraic assumptions: the
`Id`-monad scaffolding and `Std.Legacy.Range` loops reduce to `List.foldl`, and a fuel
induction carries the loop invariant "the mutable array agrees with the abstract state vector
on the live states".
-/

private theorem id_pure_eq {α : Type v} (a : α) : (pure a : Id α) = a := rfl

private theorem id_bind_eq {α β : Type v} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

private theorem id_forIn_yield_eq_foldl {α : Type v} {β : Type w} (l : List α) (f : α → β → β)
    (init : β) :
    (forIn (m := Id) l init fun a b ↦ ForInStep.yield (f a b)) =
      l.foldl (fun b a ↦ f a b) init :=
  List.forIn_pure_yield_eq_foldl f init

private theorem getD_ofFn {m : Nat} (f : Fin m → K) (s : Nat) (hs : s < m) :
    (Array.ofFn f).getD s 0 = f ⟨s, hs⟩ := by
  simp [Array.getD_eq_getD_getElem?, hs]

private theorem loop_run (chain : Chain K) :
    ∀ (remaining position : Nat) (scores : Array K), chain.len - position = remaining →
      (List.range chain.nS).foldl
          (fun b a ↦ b +
            ((List.range' position remaining 1).foldl
                (fun scores position ↦ Array.ofFn (n := chain.nS) fun next ↦
                  (List.range chain.nS).foldl
                    (fun b prior ↦ b + scores.getD prior 0 * chain.arc position prior next.val) 0)
                scores).getD a 0 *
              chain.fin a)
          0 =
        forwardFrom chain position (fun s ↦ scores.getD s 0)
  | 0, position, scores, hfuel => by
    rw [forwardFrom_of_ge chain position _ (by omega)]
    rfl
  | remaining + 1, position, scores, hfuel => by
    rw [forwardFrom_of_lt chain position _ (by omega), List.range'_succ, List.foldl_cons]
    refine (loop_run chain remaining (position + 1) _ (by omega)).trans ?_
    refine forwardFrom_congr chain (chain.len - (position + 1)) (position + 1) _ _ rfl
      fun s hs ↦ ?_
    rw [getD_ofFn _ s hs]
    show sumTo chain.nS (fun prior ↦ scores.getD prior 0 * chain.arc position prior s) = _
    rfl

/-- **Kernel refinement.**  The imperative sweep computes the functional forward recurrence.
No algebraic laws are used: this is loop bookkeeping only. -/
theorem forward_eq_forwardFun (chain : Chain K) : chain.forward = forwardFun chain := by
  unfold Chain.forward
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', id_bind_eq, id_pure_eq,
    id_forIn_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, ← List.range_eq_range']
  refine (loop_run chain (chain.len - 1) 1 _ (by omega)).trans ?_
  exact forwardFrom_congr chain (chain.len - 1) 1 _ _ rfl fun s hs ↦ getD_ofFn _ s hs

variable [LawfulChainDP K]

private theorem visit_zero_fuel (chain : Chain K) :
    ∀ (fuel position prev : Nat), chain.len - position = fuel →
      spec.visit chain position prev 0 = 0
  | 0, position, prev, hfuel => by
    rw [visit_of_ge chain prev 0 (by omega)]
    exact LawfulChainDP.zero_mul _
  | fuel + 1, position, prev, hfuel => by
    rw [visit_of_lt chain prev 0 (by omega)]
    calc sumTo chain.nS
          (fun next ↦ spec.visit chain (position + 1) next (0 * chain.arc position prev next))
        = sumTo chain.nS (fun _ ↦ (0 : K)) :=
          sumTo_congr fun next _ ↦ by
            rw [LawfulChainDP.zero_mul,
              visit_zero_fuel chain fuel (position + 1) next (by omega)]
      _ = 0 := sumTo_zero_fun chain.nS

/-- The suffix evaluator vanishes on a zero accumulated weight. -/
theorem visit_zero (chain : Chain K) (position prev : Nat) :
    spec.visit chain position prev 0 = 0 :=
  visit_zero_fuel chain (chain.len - position) position prev rfl

private theorem visit_add_fuel (chain : Chain K) :
    ∀ (fuel position prev : Nat) (a b : K), chain.len - position = fuel →
      spec.visit chain position prev (a + b) =
        spec.visit chain position prev a + spec.visit chain position prev b
  | 0, position, prev, a, b, hfuel => by
    rw [visit_of_ge chain prev (a + b) (by omega), visit_of_ge chain prev a (by omega),
      visit_of_ge chain prev b (by omega)]
    exact LawfulChainDP.add_mul a b (chain.fin prev)
  | fuel + 1, position, prev, a, b, hfuel => by
    rw [visit_of_lt chain prev (a + b) (by omega), visit_of_lt chain prev a (by omega),
      visit_of_lt chain prev b (by omega), ← sumTo_add]
    exact sumTo_congr fun next _ ↦ by
      rw [LawfulChainDP.add_mul,
        visit_add_fuel chain fuel (position + 1) next _ _ (by omega)]

/-- The suffix evaluator is additive in its accumulated weight: right distributivity propagated
through the whole recursion. -/
theorem visit_add (chain : Chain K) (position prev : Nat) (a b : K) :
    spec.visit chain position prev (a + b) =
      spec.visit chain position prev a + spec.visit chain position prev b :=
  visit_add_fuel chain (chain.len - position) position prev a b rfl

/-- The suffix evaluator commutes with finite sums of accumulated weights. -/
theorem visit_sumTo (chain : Chain K) (position prev m : Nat) (f : Nat → K) :
    spec.visit chain position prev (sumTo m f) =
      sumTo m (fun x ↦ spec.visit chain position prev (f x)) := by
  induction m with
  | zero => exact visit_zero chain position prev
  | succ k ih => rw [sumTo_succ, visit_add, ih, sumTo_succ]

private theorem sumTo_visit_run (chain : Chain K) :
    ∀ (fuel position : Nat) (w : Nat → K), chain.len - position = fuel →
      sumTo chain.nS (fun s ↦ spec.visit chain position s (w s)) =
        forwardFrom chain position w
  | 0, position, w, hfuel => by
    rw [forwardFrom, dif_pos (by omega : position ≥ chain.len)]
    exact sumTo_congr fun s _ ↦ visit_of_ge chain s (w s) (by omega)
  | fuel + 1, position, w, hfuel => by
    rw [forwardFrom, dif_neg (by omega : ¬position ≥ chain.len),
      ← sumTo_visit_run chain fuel (position + 1) (stepVec chain position w) (by omega)]
    calc sumTo chain.nS (fun s ↦ spec.visit chain position s (w s))
        = sumTo chain.nS (fun s ↦ sumTo chain.nS
            (fun next ↦ spec.visit chain (position + 1) next (w s * chain.arc position s next))) :=
          sumTo_congr fun s _ ↦ visit_of_lt chain s (w s) (by omega)
      _ = sumTo chain.nS (fun next ↦ sumTo chain.nS
            (fun s ↦ spec.visit chain (position + 1) next (w s * chain.arc position s next))) :=
          sumTo_swap chain.nS chain.nS _
      _ = sumTo chain.nS
            (fun next ↦ spec.visit chain (position + 1) next (stepVec chain position w next)) :=
          sumTo_congr fun next _ ↦ by rw [stepVec, ← visit_sumTo]

/--
**Forward-recurrence correctness.**  The exponential sum over all state sequences collapses to
the polynomial forward recurrence, over any carrier satisfying the chain-DP laws — no
multiplication associativity or left distributivity required.
-/
theorem spec_eq_forwardFun (chain : Chain K) : chain.spec = forwardFun chain := by
  show sumTo chain.nS (fun s ↦ spec.visit chain 1 s (chain.init s)) = forwardFrom chain 1 chain.init
  exact sumTo_visit_run chain (chain.len - 1) 1 chain.init rfl

/--
**End-to-end forward correctness.**  The imperative kernel `Chain.forward` computes exactly the
exponential sum over all state sequences, for every carrier satisfying the chain-DP laws.  This
composes the law-free kernel refinement with the algebraic collapse of the path sum.
-/
theorem forward_eq_spec (chain : Chain K) : chain.forward = chain.spec :=
  (forward_eq_forwardFun chain).trans (spec_eq_forwardFun chain).symm

end Chain

end Nlp
