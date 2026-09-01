import Nlp.Core.Data.FloatChart

namespace NlpTests.Core.FloatChart

open Nlp

private def chart : FloatChart := FloatChart.empty 4 3 2.25

private def updated? : Option FloatChart := chart.set? 1 3 2 9.5

private def updatedBitsAt (i j nonterminal : Nat) : Option UInt64 :=
  updated?.bind fun result ↦ (result.get? i j nonterminal).map Float.toBits

example : FloatChart.spanCount 4 = 10 := by native_decide

example : FloatChart.entryCount 4 3 = 30 := by native_decide

example : chart.cells.size = 30 := by native_decide

example : (chart.get? 0 1 0).map Float.toBits = some (2.25 : Float).toBits := by
  native_decide

example : (chart.get? 2 2 0).isNone = true := by native_decide

example : (chart.get? 0 5 0).isNone = true := by native_decide

example : (chart.get? 0 1 3).isNone = true := by native_decide

example : chart.index? 1 3 2 = some 17 := by native_decide

example : updatedBitsAt 1 3 2 = some (9.5 : Float).toBits := by native_decide

/-- Updating one address preserves a distinct cell and the allocation size. -/
example : updatedBitsAt 0 4 1 = some (2.25 : Float).toBits := by native_decide

example : (updated?.map fun result ↦ result.cells.size) = some 30 := by native_decide

example : (chart.set? 3 2 0 1.0).isNone = true := by native_decide

example : (chart.set? 0 4 3 1.0).isNone = true := by native_decide

example :
    (chart.get 1 3 2 (by omega) (by native_decide) (by native_decide)).toBits =
      (2.25 : Float).toBits := by
  native_decide

end NlpTests.Core.FloatChart
