import Nlp.Core.Algebra.Laws

/-!
# Exact min-plus cost scores

`Nlp.Cost` carries `Float` weights: fast, but its laws are only testable.  `NatCost` is the exact
tropical `(min, +)` semiring over `Nat` with a genuine infinity, so every law is a theorem.  Use
it when weights are integral — edit distance, shortest derivation length — or as the verification
twin of `Cost` in proofs about min-plus dynamic programs.
-/

namespace Nlp

/-- Exact min-plus cost.  `none` is `+∞`, the additive identity; `some c` is a finite cost. -/
structure NatCost where
  ofOption ::
  toOption : Option Nat
deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace NatCost

/-- A finite cost. -/
@[inline] def fin (cost : Nat) : NatCost := ⟨some cost⟩

/-- The unreachable cost `+∞`. -/
@[inline] def infinite : NatCost := ⟨none⟩

instance : Zero NatCost := ⟨infinite⟩
instance : One NatCost := ⟨fin 0⟩

instance : Add NatCost :=
  ⟨fun a b ↦ match a, b with
    | ⟨none⟩, b => b
    | a, ⟨none⟩ => a
    | ⟨some x⟩, ⟨some y⟩ => ⟨some (Nat.min x y)⟩⟩

instance : Mul NatCost :=
  ⟨fun a b ↦ match a, b with
    | ⟨none⟩, _ => ⟨none⟩
    | _, ⟨none⟩ => ⟨none⟩
    | ⟨some x⟩, ⟨some y⟩ => ⟨some (x + y)⟩⟩

instance : SemiringOps NatCost := {}

/-- Costs are non-negative, so the best sum of any number of repeats is taking none: `0`. -/
instance : StarOps NatCost := ⟨fun _ ↦ fin 0⟩

@[simp] theorem zero_def : (0 : NatCost) = ⟨none⟩ := rfl
@[simp] theorem one_def : (1 : NatCost) = ⟨some 0⟩ := rfl

@[simp] theorem none_add (b : NatCost) : ofOption none + b = b := by
  cases b with | ofOption o => cases o <;> rfl

@[simp] theorem add_none (a : NatCost) : a + ofOption none = a := by
  cases a with | ofOption o => cases o <;> rfl

@[simp] theorem some_add_some (x y : Nat) :
    ofOption (some x) + ofOption (some y) = ofOption (some (Nat.min x y)) := rfl

@[simp] theorem none_mul (b : NatCost) : ofOption none * b = ofOption none := by
  cases b with | ofOption o => cases o <;> rfl

@[simp] theorem mul_none (a : NatCost) : a * ofOption none = ofOption none := by
  cases a with | ofOption o => cases o <;> rfl

@[simp] theorem some_mul_some (x y : Nat) :
    ofOption (some x) * ofOption (some y) = ofOption (some (x + y)) := rfl

instance : LawfulCommSemiring NatCost where
  add_assoc a b c := by
    rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> rcases c with ⟨_ | z⟩ <;>
      simp [Nat.min_assoc]
  add_comm a b := by
    rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> simp [Nat.min_comm]
  add_zero a := by
    rcases a with ⟨_ | x⟩ <;> simp
  one_mul a := by
    rcases a with ⟨_ | x⟩ <;> simp
  zero_mul a := by
    rcases a with ⟨_ | x⟩ <;> simp
  add_mul a b c := by
    rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> rcases c with ⟨_ | z⟩ <;>
      simp [Nat.add_min_add_right]
  mul_one a := by
    rcases a with ⟨_ | x⟩ <;> simp
  mul_zero a := by
    rcases a with ⟨_ | x⟩ <;> simp
  mul_add a b c := by
    rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> rcases c with ⟨_ | z⟩ <;>
      simp [Nat.add_min_add_left]
  mul_assoc a b c := by
    rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> rcases c with ⟨_ | z⟩ <;>
      simp [Nat.add_assoc]
  mul_comm a b := by
    rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩ <;> simp [Nat.add_comm]

instance : PathProperty NatCost where
  path a b := by
    rcases a with ⟨_ | x⟩ <;> rcases b with ⟨_ | y⟩
    · exact .inl rfl
    · exact .inr rfl
    · exact .inl rfl
    · rcases Nat.le_total x y with h | h
      · exact .inl (by simp [Nat.min_eq_left h])
      · exact .inr (by simp [Nat.min_eq_right h])

instance : IdemAdd NatCost := instIdemAddOfPathProperty

instance : Bounded NatCost where
  one_add a := by
    rcases a with ⟨_ | x⟩ <;> simp [Nat.min_eq_left (Nat.zero_le _)]

end NatCost

end Nlp
