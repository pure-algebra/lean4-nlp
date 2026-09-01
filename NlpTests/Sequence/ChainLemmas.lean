import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog
import Nlp.Core.Score.NatCost
import Nlp.Sequence.ChainLemmas

/-!
The proved collapse `spec = forwardFun` and the end-to-end contract `forward = spec`
instantiate at every lawful carrier; evaluation cross-checks a few concrete chains.
-/

namespace NlpTests.Sequence.ChainLemmas

open Nlp

private def countChain : Chain Count where
  len := 3
  nS := 2
  init := fun _ ↦ ⟨1⟩
  arc := fun _ _ _ ↦ ⟨1⟩
  fin := fun _ ↦ ⟨1⟩

private def costChain : Chain NatCost where
  len := 4
  nS := 3
  init := fun state ↦ .fin state
  arc := fun position prior next ↦
    if prior == next then .fin 1 else .fin (position + next)
  fin := fun state ↦ if state == 2 then .fin 0 else .fin 5

/-- The collapse theorem applied at the exact counting carrier. -/
example : countChain.spec = countChain.forwardFun :=
  Chain.spec_eq_forwardFun countChain

/-- The collapse theorem applied at the exact min-plus carrier. -/
example : costChain.spec = costChain.forwardFun :=
  Chain.spec_eq_forwardFun costChain

/-- The end-to-end contract: the imperative kernel equals the exponential specification. -/
example : countChain.forward = countChain.spec :=
  Chain.forward_eq_spec countChain

/-- The end-to-end contract at the exact min-plus carrier. -/
example : costChain.forward = costChain.spec :=
  Chain.forward_eq_spec costChain

example : countChain.forward = countChain.forwardFun := by native_decide

example : costChain.forward = costChain.forwardFun := by native_decide

example : costChain.forward = costChain.spec := by native_decide

example : costChain.forward.toOption = some 5 := by native_decide

end NlpTests.Sequence.ChainLemmas
