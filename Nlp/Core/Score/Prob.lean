import Nlp.Core.Algebra.Ops

/-! # Linear-domain probability scores -/

namespace Nlp

/-- Linear-domain probability mass.  The unrestricted `Float` carrier has operations only. -/
structure Prob where
  ofFloat ::
  toFloat : Float
deriving Inhabited, Repr

namespace Prob

instance : Zero Prob := ⟨⟨0.0⟩⟩
instance : One Prob := ⟨⟨1.0⟩⟩
instance : Add Prob := ⟨fun a b ↦ ⟨a.toFloat + b.toFloat⟩⟩
instance : Mul Prob := ⟨fun a b ↦ ⟨a.toFloat * b.toFloat⟩⟩
instance : SemiringOps Prob := {}

end Prob

end Nlp
