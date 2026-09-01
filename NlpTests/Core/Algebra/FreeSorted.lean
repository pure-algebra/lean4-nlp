import Nlp.Core.Algebra.FreeSorted

/-! Focused checks for the free many-sorted term algebra. -/

namespace NlpTests.Core.Algebra.FreeSorted

open Nlp.FreeSorted

private inductive TestSort where
  | bit
  | pair

private inductive TestGen where
  | zero
  | one
  | flip
  | pair

private abbrev signature : Signature TestSort where
  Gen := TestGen
  output
    | .zero | .one | .flip => .bit
    | .pair => .pair
  inputs
    | .zero | .one => []
    | .flip => [.bit]
    | .pair => [.bit, .bit]

private def zero : Term signature .bit :=
  Term.op (sig := signature) TestGen.zero .nil

private def one : Term signature .bit :=
  Term.op (sig := signature) TestGen.one .nil

private def flippedZero : Term signature .bit :=
  Term.op (sig := signature) TestGen.flip (.cons zero .nil)

private def paired : Term signature .pair :=
  Term.op (sig := signature) TestGen.pair (.cons flippedZero (.cons one .nil))

private abbrev eval : Algebra signature where
  Carrier
    | .bit => Bool
    | .pair => Nat
  op
    | .zero, .nil => false
    | .one, .nil => true
    | .flip, .cons value .nil => !value
    | .pair, .cons left (.cons right .nil) =>
        (if left then 2 else 0) + if right then 1 else 0

/-- Nullary and unary generators evaluate at the declared result sort. -/
example : Term.fold eval flippedZero = true := by
  native_decide

/-- The heterogeneous fold returns a `Nat` at the second sort. -/
example : Term.fold eval paired = 3 := by
  native_decide

/-- The canonical fold is itself a homomorphism. -/
example : (foldHom eval) paired = Term.fold eval paired :=
  Hom.eq_fold (foldHom eval) paired

/-- Any homomorphism into the example algebra is determined by the generator equations. -/
example (hom : Hom signature eval) (term : Term signature s) :
    hom term = Term.fold eval term :=
  Hom.eq_fold hom term

end NlpTests.Core.Algebra.FreeSorted
