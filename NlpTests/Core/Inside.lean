import Nlp.Core.Engine.Inside

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

end NlpTests.Core.Inside
