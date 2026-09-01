import Nlp.Core.Engine.Inside
import Nlp.Core.Engine.InsideLemmas

namespace NlpTests.Core.Inside

open Nlp

private def countEdges : Array (Edge Count) :=
  #[
    ⟨0, #[], ⟨1⟩⟩,
    ⟨1, #[0], ⟨1⟩⟩,
    ⟨2, #[0], ⟨1⟩⟩,
    ⟨2, #[1], ⟨1⟩⟩
  ]

private def recogEdges : Array (Edge Recog) :=
  #[
    ⟨0, #[], ⟨true⟩⟩,
    ⟨1, #[0], ⟨true⟩⟩,
    ⟨2, #[0], ⟨false⟩⟩,
    ⟨2, #[1], ⟨true⟩⟩
  ]

private def costEdges : Array (Edge Cost) :=
  #[
    ⟨0, #[], ⟨0.0⟩⟩,
    ⟨1, #[0], ⟨1.5⟩⟩,
    ⟨2, #[0], ⟨4.0⟩⟩,
    ⟨2, #[1], ⟨2.0⟩⟩
  ]

example : (insideCount 3 countEdges).map Count.toNat = #[1, 1, 2] := by native_decide

example : (insideRecog 3 recogEdges).getD 2 0 = ⟨true⟩ := by native_decide

example :
    ((insideCost 3 costEdges).getD 2 0).toFloat.toBits = (3.5 : Float).toBits := by
  native_decide

/-! The proved refinement and its consequences instantiate at concrete carriers. -/

example : inside 3 countEdges = insideFold 3 countEdges :=
  inside_eq_insideFold 3 countEdges

example : (inside 3 countEdges).size = 3 :=
  inside_size 3 countEdges

/-- Node 4 is not the head of any edge, so its inside value is provably zero. -/
example : (inside 5 countEdges).getD 4 0 = 0 :=
  inside_getD_of_not_head 5 countEdges 4 (by decide)

/-- The example edge list is topologically ordered and in bounds, so the proved recurrence
characterizes every node value — here instantiated at the lawless Float `Cost` carrier. -/
example :
    (inside 3 costEdges).getD 2 0 =
      costEdges.toList.foldl
        (fun acc edge ↦
          if edge.head.toNat = 2 then acc + edge.contribution (inside 3 costEdges) else acc)
        0 :=
  inside_recurrence 3 costEdges (by decide) (by decide) 2

end NlpTests.Core.Inside
