import Nlp.Core.Data.StableBuckets

/-! # Stable packed-bucket tests -/

namespace NlpTests.Core.StableBuckets

open Nlp.StableBuckets

/- Empty input with zero buckets retains exactly the terminal offset. -/
#guard match build { maxBuckets := 0, maxEntries := 0 } 0 (#[] : Array Nat) id with
  | .ok layout =>
      layout.bucketCount == 0 && layout.entryCount == 0 && layout.offsets == #[0] &&
        layout.sourceOrder == #[]
  | .error _ => false

private def mixedKeys : Array Nat := #[2, 0, 2, 1, 0, 2]

private def mixedLayout : Except Error Layout :=
  build { maxBuckets := 3, maxEntries := 6 } 3 mixedKeys id

/- Counting sort retains source order within every mixed bucket. -/
#guard match mixedLayout with
  | .ok layout => layout.offsets == #[0, 2, 3, 6] && layout.sourceOrder == #[1, 4, 3, 0, 2, 5]
  | .error _ => false

/- The first invalid source is reported before a later invalid source. -/
#guard match build { maxBuckets := 3, maxEntries := 3 } 3 #[1, 4, 5] id with
  | .error (.invalidBucket 1 4 3) => true
  | _ => false

/- A nonempty source cannot select a bucket from the empty bucket space. -/
#guard match build { maxBuckets := 0, maxEntries := 1 } 0 #[0] id with
  | .error (.invalidBucket 0 0 0) => true
  | _ => false

/- The terminal offset must itself fit the runtime array-size representation. -/
#guard match build { maxBuckets := USize.size - 1, maxEntries := 0 }
    (USize.size - 1) (#[] : Array Nat) id with
  | .error (.offsetCapacity buckets) => buckets == USize.size - 1
  | _ => false

/- Exact bucket and entry budgets are inclusive. -/
#guard (build { maxBuckets := 3, maxEntries := 6 } 3 mixedKeys id).isOk

/- A one-bucket-short policy reports the exact requirement and limit. -/
#guard match build { maxBuckets := 2, maxEntries := 6 } 3 mixedKeys id with
  | .error (.bucketBudget 3 2) => true
  | _ => false

/- A one-entry-short policy reports the exact requirement and limit. -/
#guard match build { maxBuckets := 3, maxEntries := 5 } 3 mixedKeys id with
  | .error (.entryBudget 6 5) => true
  | _ => false

/- Projection rejects a misaligned parallel column before producing output. -/
#guard match mixedLayout with
  | .error _ => false
  | .ok layout =>
      match layout.gatherMap #["a", "b"] (fun value ↦ value ++ "!") with
      | .error (.columnSize 6 2) => true
      | _ => false

/- Projection follows the stable source permutation without a caller-provided default. -/
#guard match mixedLayout with
  | .error _ => false
  | .ok layout =>
      match layout.gatherMap #["a", "b", "c", "d", "e", "f"] (fun value ↦ value ++ "!") with
      | .ok output => output == #["b!", "e!", "d!", "a!", "c!", "f!"]
      | .error _ => false

/-- A payload intentionally lacking an `Inhabited` instance. -/
private structure Payload where
  bucket : Nat
  value : Nat
  deriving DecidableEq

/- Neither layout construction nor projection requires a caller payload default. -/
#guard match build { maxBuckets := 2, maxEntries := 3 } 2
    #[Payload.mk 1 4, Payload.mk 0 7, Payload.mk 1 9] (fun item ↦ item.bucket) with
  | .error _ => false
  | .ok layout =>
      match layout.gatherMap #[Payload.mk 1 4, Payload.mk 0 7, Payload.mk 1 9] id with
      | .ok output => output == #[Payload.mk 0 7, Payload.mk 1 4, Payload.mk 1 9]
      | .error _ => false

/-- Independent stable-bucket ordering oracle used for the high-fanout case. -/
private def expectedOrder (bucketCount : Nat) (keys : Array Nat) : Array Nat := Id.run do
  let mut output := #[]
  for bucket in [0:bucketCount] do
    for source in [0:keys.size] do
      if keys[source]! == bucket then
        output := output.push source
  return output

/-- One large bucket interspersed with a smaller bucket exercises stable cursor advancement. -/
private def highFanoutKeys : Array Nat :=
  (List.range 2048).toArray.map fun source ↦ if source % 17 == 0 then 0 else 3

/- High fan-out construction agrees with an independent bucket-major stable oracle. -/
#guard match build { maxBuckets := 4, maxEntries := 2048 } 4 highFanoutKeys id with
  | .ok layout =>
      layout.sourceOrder == expectedOrder 4 highFanoutKeys && layout.offsets.back? == some 2048
  | .error _ => false

/- Valid empty and nonempty ranges remain distinguishable from an invalid bucket. -/
#guard match build { maxBuckets := 4, maxEntries := 2 } 4 #[2, 2] id with
  | .error _ => false
  | .ok layout =>
      (layout.range? 0).map (fun range ↦ (range.first, range.stop)) == some (0, 0) &&
        (layout.range? 1).map (fun range ↦ (range.first, range.stop)) == some (0, 0) &&
        (layout.range? 2).map (fun range ↦ (range.first, range.stop)) == some (0, 2) &&
        (layout.range? 3).map (fun range ↦ (range.first, range.stop)) == some (2, 2) &&
        layout.range? 4 == none

/- Checked range size is the half-open offset difference. -/
#guard match mixedLayout.toOption.bind (fun layout ↦ layout.range? 2) with
  | some range => range.size == 3
  | none => false

end NlpTests.Core.StableBuckets
