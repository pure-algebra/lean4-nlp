/-!
# Monoids and monoid homomorphisms

This small kernel is enough to express chunkable folds without importing a larger algebra
hierarchy.
-/

namespace Nlp

/-- A multiplicative monoid built from Lean's core `Mul` and `One` operations. -/
class Monoid0 (M : Type u) extends Mul M, One M where
  mul_assoc : ∀ a b c : M, (a * b) * c = a * (b * c)
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

/-- The free monoid over an alphabet. -/
abbrev FreeMon (A : Type u) := List A

/-- Map generators into a monoid and combine them in input order. -/
@[specialize]
def foldMap {A : Type u} {M : Type v} [Monoid0 M] (f : A → M) : FreeMon A → M
  | [] => 1
  | a :: as => f a * foldMap f as

/-- `foldMap` preserves concatenation, licensing chunk-and-combine evaluation. -/
theorem foldMap_append {A : Type u} {M : Type v} [Monoid0 M]
    (f : A → M) (xs ys : FreeMon A) :
    foldMap f (xs ++ ys) = foldMap f xs * foldMap f ys := by
  induction xs with
  | nil => simp [foldMap, Monoid0.one_mul]
  | cons a as ih => simp [foldMap, ih, Monoid0.mul_assoc]

/-- A homomorphism between multiplicative monoids. -/
structure MonHom (M : Type u) (N : Type v) [Monoid0 M] [Monoid0 N] where
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b

instance [Monoid0 M] [Monoid0 N] : CoeFun (MonHom M N) (fun _ ↦ M → N) :=
  ⟨MonHom.toFun⟩

namespace MonHom

/-- The identity monoid homomorphism. -/
def id (M : Type u) [Monoid0 M] : MonHom M M where
  toFun := fun x ↦ x
  map_one := rfl
  map_mul _ _ := rfl

/-- Composition of monoid homomorphisms. -/
def comp [Monoid0 M] [Monoid0 N] [Monoid0 P]
    (g : MonHom N P) (f : MonHom M N) : MonHom M P where
  toFun := fun x ↦ g (f x)
  map_one := by rw [f.map_one, g.map_one]
  map_mul a b := by rw [f.map_mul, g.map_mul]

end MonHom

end Nlp
