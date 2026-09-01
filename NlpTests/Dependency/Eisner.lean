import Nlp.Core.Score.Count
import Nlp.Core.Score.NatCost
import Nlp.Core.Score.Recog
import Nlp.Dependency.Eisner

namespace NlpTests.Dependency.Eisner

open Nlp Nlp.Dependency.Eisner

/-- Fully connected unit-weight dependency system for exact projective-tree counting. -/
private def allCount (n : Nat) : ArcWeights Count where
  n
  rootWeight := fun _ ↦ 1
  tokenWeight := fun head dependent ↦ if head == dependent then 0 else 1

example : (inside (allCount 0)).toNat = 0 := by native_decide
example : (inside (allCount 1)).toNat = 1 := by native_decide
example : (inside (allCount 2)).toNat = 2 := by native_decide
example : (inside (allCount 3)).toNat = 7 := by native_decide
example : (inside (allCount 4)).toNat = 30 := by native_decide
example : (inside (allCount 5)).toNat = 143 := by native_decide

/-- With the middle token forced as root, three tokens have one projective star. -/
private def middleRootCount : ArcWeights Count where
  n := 3
  rootWeight := fun dependent ↦ if dependent == 1 then 1 else 0
  tokenWeight := fun head dependent ↦ if head == dependent then 0 else 1

example : (inside middleRootCount).toNat = 1 := by native_decide

/-- Recognition fixture with the middle token governing both neighbors. -/
private def forcedRecognized : ArcWeights Recog where
  n := 3
  rootWeight := fun dependent ↦ ⟨dependent == 1⟩
  tokenWeight := fun head dependent ↦
    ⟨head == 1 && (dependent == 0 || dependent == 2)⟩

example : (inside forcedRecognized).toBool = true := by native_decide

/-- Removing the only arc to token two makes the forced-root system unreachable. -/
private def forcedRejected : ArcWeights Recog where
  n := 3
  rootWeight := fun dependent ↦ ⟨dependent == 1⟩
  tokenWeight := fun head dependent ↦ ⟨head == 1 && dependent == 0⟩

example : (inside forcedRejected).toBool = false := by native_decide

/-- Exact min-plus fixture: root cost three plus two forced unit arcs. -/
private def forcedCost : ArcWeights NatCost where
  n := 3
  rootWeight := fun dependent ↦
    if dependent == 1 then NatCost.fin 3 else NatCost.infinite
  tokenWeight := fun head dependent ↦
    if head == 1 && (dependent == 0 || dependent == 2) then
      NatCost.fin 1
    else
      NatCost.infinite

example : (inside forcedCost).toOption = some 5 := by native_decide

private def countChart : Chart Count (allCount 3).n := insideChart (allCount 3)

/-- Four item values are retained for each inclusive span. -/
example : countChart.storageSize = entryCount 3 := by
  rw [Chart.storageSize_eq]
  rfl

/-- Singleton complete items carry the multiplicative identity. -/
example : countChart.completeHeadLeft? 1 1 = some 1 := by native_decide
example : countChart.completeHeadRight? 1 1 = some 1 := by native_decide

/-- Checked chart projection rejects reversed and out-of-range inclusive spans. -/
example : countChart.completeHeadLeft? 2 1 = none := by native_decide
example : countChart.completeHeadRight? 0 3 = none := by native_decide

/-- Safe arc projections reject self arcs and preserve in-range collapsed weights. -/
example : (allCount 3).tokenWeight? 1 1 = none := by native_decide
example : (allCount 3).tokenWeight? 1 2 = some 1 := by native_decide
example : (allCount 3).rootWeight? 3 = none := by native_decide

end NlpTests.Dependency.Eisner
