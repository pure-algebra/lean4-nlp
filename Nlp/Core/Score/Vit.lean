import Nlp.Core.Algebra.Ops

/-! # Linear-domain Viterbi scores -/

namespace Nlp

/-- A Viterbi probability score using max for choice and multiplication for sequencing. -/
structure Vit where
  ofFloat ::
  toFloat : Float
deriving Inhabited, Repr

namespace Vit

instance : Zero Vit := ⟨⟨0.0⟩⟩
instance : One Vit := ⟨⟨1.0⟩⟩
instance : Add Vit := ⟨fun a b ↦ ⟨if a.toFloat ≤ b.toFloat then b.toFloat else a.toFloat⟩⟩
instance : Mul Vit := ⟨fun a b ↦ ⟨a.toFloat * b.toFloat⟩⟩
instance : SemiringOps Vit := {}
instance : StarOps Vit := ⟨fun _ ↦ ⟨1.0⟩⟩

end Vit

end Nlp
