import Nlp.Core.Algebra.Laws

/-! # Recognition score domain -/

namespace Nlp

/-- Recognition: alternative derivations use disjunction and composed steps use conjunction. -/
structure Recog where
  ofBool ::
  toBool : Bool
deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Recog

instance : Zero Recog := ⟨⟨false⟩⟩
instance : One Recog := ⟨⟨true⟩⟩
instance : Add Recog := ⟨fun a b ↦ ⟨a.toBool || b.toBool⟩⟩
instance : Mul Recog := ⟨fun a b ↦ ⟨a.toBool && b.toBool⟩⟩
instance : SemiringOps Recog := {}
instance : StarOps Recog := ⟨fun _ ↦ ⟨true⟩⟩

instance : LawfulSemiring Recog where
  add_assoc a b c := by
    cases a with | ofBool x => cases b with | ofBool y => cases c with
      | ofBool z => cases x <;> cases y <;> cases z <;> rfl
  add_comm a b := by
    cases a with | ofBool x => cases b with
      | ofBool y => cases x <;> cases y <;> rfl
  add_zero a := by
    cases a with | ofBool x => cases x <;> rfl
  one_mul a := by
    cases a with | ofBool x => cases x <;> rfl
  zero_mul a := by
    cases a with | ofBool x => cases x <;> rfl
  add_mul a b c := by
    cases a with | ofBool x => cases b with | ofBool y => cases c with
      | ofBool z => cases x <;> cases y <;> cases z <;> rfl
  mul_one a := by
    cases a with | ofBool x => cases x <;> rfl
  mul_zero a := by
    cases a with | ofBool x => cases x <;> rfl
  mul_add a b c := by
    cases a with | ofBool x => cases b with | ofBool y => cases c with
      | ofBool z => cases x <;> cases y <;> cases z <;> rfl
  mul_assoc a b c := by
    cases a with | ofBool x => cases b with | ofBool y => cases c with
      | ofBool z => cases x <;> cases y <;> cases z <;> rfl

instance : IdemAdd Recog where
  add_idem a := by
    cases a with | ofBool x => cases x <;> rfl

instance : PathProperty Recog where
  path a b := by
    cases a with | ofBool x => cases b with
      | ofBool y => cases x <;> cases y <;> simp [HAdd.hAdd, Add.add]

end Recog

end Nlp
