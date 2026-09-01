import Nlp.Core.Algebra.Laws

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

/-- Addition selects one of its arguments — provable with no `Float` arithmetic, because the
`if` returns one branch's payload and structure eta restores the argument. -/
instance : PathProperty Vit where
  path a b := by
    cases a with | ofFloat x => cases b with | ofFloat y =>
      show Vit.ofFloat (if x ≤ y then y else x) = _ ∨
        Vit.ofFloat (if x ≤ y then y else x) = _
      split
      · exact .inr rfl
      · exact .inl rfl

/-- Idempotence is inherited from the path property. -/
instance : IdemAdd Vit := instIdemAddOfPathProperty

end Vit

end Nlp
