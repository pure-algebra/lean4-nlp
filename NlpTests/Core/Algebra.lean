import Nlp.Core.Algebra.Monoid
import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog

namespace NlpTests.Core.Algebra

open Nlp

example : SemiringOps Recog := inferInstance
example : LawfulSemiring Recog := inferInstance
example : SemiringOps Count := inferInstance
example : LawfulCommSemiring Count := inferInstance

/-- The bridge to `Std.Associative` makes the core array theorem directly reusable. -/
example (xs ys : Array Count) : (xs ++ ys).sum = xs.sum + ys.sum :=
  Array.sum_append

private structure AddNat where
  value : Nat
deriving DecidableEq

namespace AddNat

instance : Mul AddNat := ⟨fun a b ↦ ⟨a.value + b.value⟩⟩
instance : One AddNat := ⟨⟨0⟩⟩

instance : Monoid0 AddNat where
  mul_assoc a b c := congrArg AddNat.mk (Nat.add_assoc a.value b.value c.value)
  one_mul a := congrArg AddNat.mk (Nat.zero_add a.value)
  mul_one a := congrArg AddNat.mk (Nat.add_zero a.value)

end AddNat

example : (foldMap AddNat.mk [1, 2, 3]).value = 6 := by native_decide

example :
    foldMap AddNat.mk ([1, 2] ++ [3, 4]) =
      foldMap AddNat.mk [1, 2] * foldMap AddNat.mk [3, 4] :=
  foldMap_append AddNat.mk [1, 2] [3, 4]

end NlpTests.Core.Algebra
