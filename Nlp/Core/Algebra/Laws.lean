import Nlp.Core.Algebra.Ops

/-!
# Laws for semiring operations

These classes are `Prop`-valued and erased at runtime.  The hierarchy follows the audited split:
the left-fold dynamic-programming laws, then every semiring law except multiplication
associativity, then a full semiring, then a commutative semiring.
-/

namespace Nlp

universe u

variable {K : Type u}

/-- Left distributivity, indexed by the two operations rather than a carrier bundle. -/
class LeftDistrib (mul add : K → K → K) : Prop where
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

/-- Right distributivity, indexed by the two operations rather than a carrier bundle. -/
class RightDistrib (mul add : K → K → K) : Prop where
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)

/-- `z` annihilates `mul` on the left. -/
class LeftAnnihilator (mul : K → K → K) (z : outParam K) : Prop where
  left_absorb : ∀ a, mul z a = z

/-- `z` annihilates `mul` on the right. -/
class RightAnnihilator (mul : K → K → K) (z : outParam K) : Prop where
  right_absorb : ∀ a, mul a z = z

export LeftDistrib (left_distrib)
export RightDistrib (right_distrib)
export LeftAnnihilator (left_absorb)
export RightAnnihilator (right_absorb)

/-- Exactly the laws required by a left-fold chain or acyclic-hypergraph dynamic program. -/
class LawfulChainDP (K : Type u) [SemiringOps K] : Prop where
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : K, a + b = b + a
  add_zero : ∀ a : K, a + 0 = a
  one_mul : ∀ a : K, (1 : K) * a = a
  zero_mul : ∀ a : K, (0 : K) * a = 0
  add_mul : ∀ a b c : K, (a + b) * c = a * c + b * c

/-- Every semiring law except associativity of multiplication. -/
class LawfulSemiringMinusAssoc (K : Type u) [SemiringOps K] : Prop
    extends LawfulChainDP K where
  mul_one : ∀ a : K, a * 1 = a
  mul_zero : ∀ a : K, a * (0 : K) = 0
  mul_add : ∀ a b c : K, a * (b + c) = a * b + a * c

/-- The full semiring laws. -/
class LawfulSemiring (K : Type u) [SemiringOps K] : Prop
    extends LawfulSemiringMinusAssoc K where
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)

/-- A semiring whose multiplication is commutative. -/
class LawfulCommSemiring (K : Type u) [SemiringOps K] : Prop
    extends LawfulSemiring K where
  mul_comm : ∀ a b : K, a * b = b * a

/-- Addition is idempotent. -/
class IdemAdd (K : Type u) [Add K] : Prop where
  add_idem : ∀ a : K, a + a = a

/-- Addition always selects one of its arguments. -/
class PathProperty (K : Type u) [Add K] : Prop where
  path : ∀ a b : K, a + b = a ∨ a + b = b

/-- The multiplicative unit annihilates addition. -/
class Bounded (K : Type u) [SemiringOps K] : Prop where
  one_add : ∀ a : K, 1 + a = 1

/-- Path-selecting addition is idempotent: `a + a` must return one of its two equal arguments. -/
instance (priority := low) instIdemAddOfPathProperty [Add K] [PathProperty K] : IdemAdd K where
  add_idem a := by rcases PathProperty.path a a with h | h <;> exact h

/-- In a bounded semiring the unit also annihilates addition on the right. -/
theorem Bounded.add_one [SemiringOps K] [LawfulChainDP K] [Bounded K] (a : K) :
    a + 1 = 1 :=
  (LawfulChainDP.add_comm a 1).trans (Bounded.one_add a)

/-! ## Bridges to operation-indexed core and `Std` laws -/

instance instAssociativeAdd [SemiringOps K] [LawfulChainDP K] :
    Std.Associative (α := K) (fun a b ↦ a + b) :=
  ⟨LawfulChainDP.add_assoc⟩

instance instCommutativeAdd [SemiringOps K] [LawfulChainDP K] :
    Std.Commutative (α := K) (fun a b ↦ a + b) :=
  ⟨LawfulChainDP.add_comm⟩

instance instLawfulIdentityAdd [SemiringOps K] [LawfulChainDP K] :
    Std.LawfulIdentity (α := K) (fun a b ↦ a + b) 0 where
  left_id a := (LawfulChainDP.add_comm 0 a).trans (LawfulChainDP.add_zero a)
  right_id := LawfulChainDP.add_zero

instance instAssociativeMul [SemiringOps K] [LawfulSemiring K] :
    Std.Associative (α := K) (fun a b ↦ a * b) :=
  ⟨LawfulSemiring.mul_assoc⟩

instance instLawfulIdentityMul [SemiringOps K] [LawfulSemiringMinusAssoc K] :
    Std.LawfulIdentity (α := K) (fun a b ↦ a * b) 1 where
  left_id := LawfulChainDP.one_mul
  right_id := LawfulSemiringMinusAssoc.mul_one

instance instIdempotentAdd [SemiringOps K] [IdemAdd K] :
    Std.IdempotentOp (α := K) (fun a b ↦ a + b) :=
  ⟨IdemAdd.add_idem⟩

instance instLeftDistrib [SemiringOps K] [LawfulSemiringMinusAssoc K] :
    LeftDistrib (K := K) (fun a b ↦ a * b) (fun a b ↦ a + b) :=
  ⟨LawfulSemiringMinusAssoc.mul_add⟩

instance instRightDistrib [SemiringOps K] [LawfulChainDP K] :
    RightDistrib (K := K) (fun a b ↦ a * b) (fun a b ↦ a + b) :=
  ⟨LawfulChainDP.add_mul⟩

instance instLeftAnnihilator [SemiringOps K] [LawfulChainDP K] :
    LeftAnnihilator (K := K) (fun a b ↦ a * b) 0 :=
  ⟨LawfulChainDP.zero_mul⟩

instance instRightAnnihilator [SemiringOps K] [LawfulSemiringMinusAssoc K] :
    RightAnnihilator (K := K) (fun a b ↦ a * b) 0 :=
  ⟨LawfulSemiringMinusAssoc.mul_zero⟩

end Nlp
