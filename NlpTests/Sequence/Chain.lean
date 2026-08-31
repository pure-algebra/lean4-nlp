import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog
import Nlp.Core.Score.Vit
import Nlp.Sequence.Chain

namespace NlpTests.Sequence.Chain

open Nlp

private def countChain : Chain Count where
  len := 3
  nS := 2
  init := fun _ ↦ ⟨1⟩
  arc := fun _ _ _ ↦ ⟨1⟩
  fin := fun _ ↦ ⟨1⟩

private def recogChain : Chain Recog where
  len := 3
  nS := 2
  init := fun state ↦ ⟨state == 0⟩
  arc := fun _ prior next ↦ ⟨prior == next⟩
  fin := fun state ↦ ⟨state == 0⟩

private def vitChain : Chain Vit where
  len := 2
  nS := 2
  init := fun state ↦ if state == 0 then ⟨0.5⟩ else ⟨0.25⟩
  arc := fun _ prior next ↦ if prior == next then ⟨0.5⟩ else ⟨0.25⟩
  fin := fun _ ↦ ⟨1.0⟩

example : countChain.forward.toNat = 8 := by native_decide

example : countChain.forward = countChain.spec := by native_decide

example : recogChain.forward = ⟨true⟩ := by native_decide

example : recogChain.forward = recogChain.spec := by native_decide

example : vitChain.forward.toFloat.toBits = vitChain.spec.toFloat.toBits := by native_decide

end NlpTests.Sequence.Chain
