import Nlp.Core.Algebra.Laws

/-! # Derivation-counting score domain -/

namespace Nlp

/-- Exact derivation counts, kept distinct from unrelated natural numbers. -/
structure Count where
  ofNat ::
  toNat : Nat
deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Count

instance : Zero Count := ⟨⟨0⟩⟩
instance : One Count := ⟨⟨1⟩⟩
instance : Add Count := ⟨fun a b ↦ ⟨a.toNat + b.toNat⟩⟩
instance : Mul Count := ⟨fun a b ↦ ⟨a.toNat * b.toNat⟩⟩
instance : SemiringOps Count := {}

instance : LawfulCommSemiring Count where
  add_assoc a b c := congrArg ofNat (Nat.add_assoc a.toNat b.toNat c.toNat)
  add_comm a b := congrArg ofNat (Nat.add_comm a.toNat b.toNat)
  add_zero a := congrArg ofNat (Nat.add_zero a.toNat)
  one_mul a := congrArg ofNat (Nat.one_mul a.toNat)
  zero_mul a := congrArg ofNat (Nat.zero_mul a.toNat)
  add_mul a b c := congrArg ofNat (Nat.add_mul a.toNat b.toNat c.toNat)
  mul_one a := congrArg ofNat (Nat.mul_one a.toNat)
  mul_zero a := congrArg ofNat (Nat.mul_zero a.toNat)
  mul_add a b c := congrArg ofNat (Nat.mul_add a.toNat b.toNat c.toNat)
  mul_assoc a b c := congrArg ofNat (Nat.mul_assoc a.toNat b.toNat c.toNat)
  mul_comm a b := congrArg ofNat (Nat.mul_comm a.toNat b.toNat)

end Count

end Nlp
