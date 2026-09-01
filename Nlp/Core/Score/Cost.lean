import Nlp.Core.Algebra.Laws

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

/-- Addition selects one of its arguments — provable with no `Float` arithmetic, because the
`if` returns one branch's payload and structure eta restores the argument. -/
instance : PathProperty Cost where
  path a b := by
    cases a with | ofFloat x => cases b with | ofFloat y =>
      show Cost.ofFloat (if x ≤ y then x else y) = _ ∨
        Cost.ofFloat (if x ≤ y then x else y) = _
      split
      · exact .inl rfl
      · exact .inr rfl

/-- Idempotence is inherited from the path property. -/
instance : IdemAdd Cost := instIdemAddOfPathProperty

end Cost

end Nlp
