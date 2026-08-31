import Nlp.Core.Algebra.Ops

/-! # Log-domain probability scores -/

namespace Nlp

/-- Negative infinity, hoisted so hot loops do not repeatedly construct the value. -/
def ninf : Float := -1.0 / 0.0

/-- A log-domain probability score.  The unrestricted `Float` carrier has operations only. -/
structure LogProb where
  ofFloat ::
  toFloat : Float
deriving Inhabited, Repr

namespace LogProb

/-- Stable binary log-sum-exp.  The infinity guards preserve the additive identity. -/
@[inline] def lse (x y : Float) : Float :=
  if x == ninf then y
  else if y == ninf then x
  else
    let m := if x ≤ y then y else x
    let d := if x ≤ y then x - y else y - x
    m + Float.log (1.0 + Float.exp d)

instance : Zero LogProb := ⟨⟨ninf⟩⟩
instance : One LogProb := ⟨⟨0.0⟩⟩
instance : Add LogProb := ⟨fun a b ↦ ⟨lse a.toFloat b.toFloat⟩⟩
instance : Mul LogProb := ⟨fun a b ↦ ⟨a.toFloat + b.toFloat⟩⟩
instance : SemiringOps LogProb := {}

end LogProb

end Nlp
