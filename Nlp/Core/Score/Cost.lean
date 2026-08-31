import Nlp.Core.Algebra.Ops

/-! # Min-plus cost scores -/

namespace Nlp

/-- Positive infinity, hoisted so hot loops do not repeatedly construct the value. -/
def inf : Float := 1.0 / 0.0

/-- Non-negative min-plus cost.  The unrestricted `Float` carrier has operations only. -/
structure Cost where
  ofFloat ::
  toFloat : Float
deriving Inhabited, Repr

namespace Cost

instance : Zero Cost := ⟨⟨inf⟩⟩
instance : One Cost := ⟨⟨0.0⟩⟩
instance : Add Cost := ⟨fun a b ↦ ⟨if a.toFloat ≤ b.toFloat then a.toFloat else b.toFloat⟩⟩
instance : Mul Cost := ⟨fun a b ↦ ⟨a.toFloat + b.toFloat⟩⟩
instance : SemiringOps Cost := {}
instance : StarOps Cost := ⟨fun _ ↦ ⟨0.0⟩⟩

/-- The natural min-plus order: lower numeric costs are better. -/
instance : LE Cost := ⟨fun a b ↦ b.toFloat ≤ a.toFloat⟩

end Cost

end Nlp
