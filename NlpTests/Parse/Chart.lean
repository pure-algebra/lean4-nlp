import Nlp.Parse.Chart

namespace NlpTests.Parse.Chart

open Nlp.Parse

example : Chart.cellCount 0 = 0 := by native_decide
example : Chart.cellCount 5 = 15 := by native_decide
example : Chart.entryCount 5 6 = 90 := by native_decide

private def indicesForFive : Array Nat :=
  #[ Chart.tri 5 0 1, Chart.tri 5 1 2, Chart.tri 5 2 3, Chart.tri 5 3 4,
     Chart.tri 5 4 5, Chart.tri 5 0 2, Chart.tri 5 1 3, Chart.tri 5 2 4,
     Chart.tri 5 3 5, Chart.tri 5 0 3, Chart.tri 5 1 4, Chart.tri 5 2 5,
     Chart.tri 5 0 4, Chart.tri 5 1 5, Chart.tri 5 0 5 ]

/-- Every valid span at `n = 5` occupies exactly one consecutive triangular cell. -/
example : indicesForFive = Array.range 15 := by native_decide

example : Chart.cidx 5 6 0 5 4 = 88 := by native_decide

end NlpTests.Parse.Chart
