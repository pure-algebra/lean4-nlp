import Nlp.Core.Algebra.Laws

/-!
# Left-fold indexed sums

`sumTo m f` is the left-fold sum `0 + f 0 + f 1 + ⋯ + f (m - 1)` — exactly the accumulation
shape produced by the dynamic-programming kernels and by `Chain.spec`.  The lemmas here are the
complete interchange toolkit needed to collapse exponential path sums into forward recurrences:
congruence, additivity, right distribution, and Fubini-style swap.  Everything is proved from
`LawfulChainDP` alone — in particular no multiplication associativity and no left
distributivity, so the lemmas apply to every chain-DP carrier.
-/

namespace Nlp

universe u

variable {K : Type u} [SemiringOps K]

/-- Left-fold sum of `f` over `0, …, m - 1`, in the shape used by specs and kernels. -/
def sumTo (m : Nat) (f : Nat → K) : K :=
  (List.range m).foldl (fun total s ↦ total + f s) 0

@[simp] theorem sumTo_zero (f : Nat → K) : sumTo 0 f = 0 := rfl

theorem sumTo_succ (m : Nat) (f : Nat → K) : sumTo (m + 1) f = sumTo m f + f m := by
  unfold sumTo
  rw [List.range_succ, List.foldl_append]
  rfl

theorem sumTo_congr {m : Nat} {f g : Nat → K} (h : ∀ s, s < m → f s = g s) :
    sumTo m f = sumTo m g := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ, sumTo_succ, ih (fun s hs ↦ h s (Nat.lt_succ_of_lt hs)),
      h k (Nat.lt_succ_self k)]

section Laws

variable [LawfulChainDP K]

/-- Rearrange a four-way sum; the only shuffle the interchange lemmas need. -/
private theorem add_add_add (a b c d : K) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [LawfulChainDP.add_assoc a b (c + d), ← LawfulChainDP.add_assoc b c d,
    LawfulChainDP.add_comm b c, LawfulChainDP.add_assoc c b d,
    ← LawfulChainDP.add_assoc a c (b + d)]

theorem sumTo_zero_fun (m : Nat) : sumTo m (fun _ ↦ (0 : K)) = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => rw [sumTo_succ, ih, LawfulChainDP.add_zero]

theorem sumTo_add (m : Nat) (f g : Nat → K) :
    sumTo m (fun s ↦ f s + g s) = sumTo m f + sumTo m g := by
  induction m with
  | zero => exact (LawfulChainDP.add_zero (0 : K)).symm
  | succ k ih => rw [sumTo_succ, sumTo_succ, sumTo_succ, ih, add_add_add]

/-- Right distribution: a common factor on the right moves inside the sum. -/
theorem sumTo_mul_right (m : Nat) (f : Nat → K) (c : K) :
    sumTo m f * c = sumTo m (fun s ↦ f s * c) := by
  induction m with
  | zero => exact LawfulChainDP.zero_mul c
  | succ k ih => rw [sumTo_succ, sumTo_succ, LawfulChainDP.add_mul, ih]

/-- Fubini for rectangular index sets. -/
theorem sumTo_swap (m k : Nat) (f : Nat → Nat → K) :
    sumTo m (fun a ↦ sumTo k (f a)) = sumTo k (fun b ↦ sumTo m (fun a ↦ f a b)) := by
  induction m with
  | zero => exact (sumTo_zero_fun k).symm
  | succ j ih =>
    rw [sumTo_succ, ih, ← sumTo_add]
    exact sumTo_congr fun b _ ↦ (sumTo_succ j (fun a ↦ f a b)).symm

end Laws

end Nlp
