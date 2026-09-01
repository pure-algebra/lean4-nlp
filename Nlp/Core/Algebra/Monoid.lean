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

/-! ## The universal property of the free monoid

`FreeMon A` really is free: with concatenation it is a monoid, `foldMap f` is a homomorphism
extending `f`, homomorphisms commute with `foldMap`, and every homomorphism out of `FreeMon A`
is a `foldMap`.  These four facts license every chunk-and-combine evaluation strategy: any
per-chunk summary that is a homomorphism can be recombined in any bracketing.
-/

instance {A : Type u} : Monoid0 (FreeMon A) where
  mul := List.append
  one := []
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

@[simp] theorem foldMap_one {A : Type u} {M : Type v} [Monoid0 M] (f : A → M) :
    foldMap f (1 : FreeMon A) = 1 := rfl

@[simp] theorem foldMap_singleton {A : Type u} {M : Type v} [Monoid0 M] (f : A → M) (a : A) :
    foldMap f [a] = f a := by
  simp [foldMap, Monoid0.mul_one]

/-- `foldMap f` packaged as the homomorphism extending `f` along singletons. -/
def foldMapHom {A : Type u} {M : Type v} [Monoid0 M] (f : A → M) : MonHom (FreeMon A) M where
  toFun := foldMap f
  map_one := rfl
  map_mul := foldMap_append f

/-- Homomorphisms commute with `foldMap`: summarize chunks first or last, the result agrees. -/
theorem MonHom.toFun_foldMap {A : Type u} {M : Type v} {N : Type w}
    [Monoid0 M] [Monoid0 N] (h : MonHom M N) (f : A → M) (xs : FreeMon A) :
    h.toFun (foldMap f xs) = foldMap (fun a ↦ h.toFun (f a)) xs := by
  induction xs with
  | nil => exact h.map_one
  | cons a as ih => rw [foldMap, foldMap, h.map_mul, ih]

/-- Uniqueness half of the universal property: a homomorphism out of the free monoid is
determined by its values on singletons, and is a `foldMap`. -/
theorem MonHom.eq_foldMap {A : Type u} {M : Type v} [Monoid0 M]
    (h : MonHom (FreeMon A) M) (xs : FreeMon A) :
    h.toFun xs = foldMap (fun a ↦ h.toFun [a]) xs := by
  induction xs with
  | nil => exact h.map_one
  | cons a as ih =>
    rw [foldMap, ← ih]
    exact h.map_mul [a] as

end Nlp
