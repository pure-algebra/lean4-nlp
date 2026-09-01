import Nlp.Core.Score.NatCost

/-! Exact min-plus carrier: law instances resolve, and small computations behave tropically. -/

namespace NlpTests.Core.NatCost

open Nlp

example : SemiringOps NatCost := inferInstance
example : LawfulCommSemiring NatCost := inferInstance
example : IdemAdd NatCost := inferInstance
example : PathProperty NatCost := inferInstance
example : Bounded NatCost := inferInstance

example : Nlp.NatCost.fin 3 + Nlp.NatCost.fin 5 = Nlp.NatCost.fin 3 := by native_decide
example : Nlp.NatCost.fin 3 * Nlp.NatCost.fin 5 = Nlp.NatCost.fin 8 := by native_decide
example : (0 : NatCost) + Nlp.NatCost.fin 7 = Nlp.NatCost.fin 7 := by native_decide
example : (0 : NatCost) * Nlp.NatCost.fin 7 = 0 := by native_decide
example : (1 : NatCost) + Nlp.NatCost.fin 7 = 1 := by native_decide

/-- Distributivity turns "best of two continuations after a shared prefix" into a single best. -/
example :
    Nlp.NatCost.fin 2 * (Nlp.NatCost.fin 4 + Nlp.NatCost.fin 1) =
      Nlp.NatCost.fin 2 * Nlp.NatCost.fin 4 + Nlp.NatCost.fin 2 * Nlp.NatCost.fin 1 :=
  LawfulSemiringMinusAssoc.mul_add _ _ _

end NlpTests.Core.NatCost
