import Nlp.Core.Data.StableBuckets

/-!
# Stable packed-bucket benchmark

This native benchmark compares `StableBuckets.build` with an independently shaped reference
that first accumulates source ordinals in `Array (Array Nat)` rows and then flattens them. Source
fixtures are constructed before timing. Timed build lanes include validation, grouping, offsets,
and stable source-order construction for both implementations.

A build-only crossover sweep uses exact bucket/entry ratios 1, 2, 4, and 8. Every three-entry
group creates one singleton bucket and one two-entry bucket, matching Automaton's low-fanout
transition rows while spreading populated buckets across the full state space.

The final lane builds both layouts before timing, then compares three complete projected columns:
`Layout.gatherMap` against projection through the reference source order. Every lane establishes
exact parity before warmup, checks every timed result, consumes complete outputs in a checksum,
and asserts no machine-specific performance threshold.

The retained-representation lanes model Unary's indexing seam. The old lane times construction
and bucket-major traversal of retained nested value rows without flattening. The packed lane times
`StableBuckets.build`, `gatherMap id`, and traversal of retained offsets plus flat values. Untimed
setup alone flattens the nested form to establish exact offsets, sentinel, and entry parity.
-/

namespace StableBucketsBenchmark

open Nlp

private structure Entry where
  bucket : Nat
  first : Nat
  second : UInt64
  deriving Repr, DecidableEq

private structure Fixture where
  name : String
  bucketCount : Nat
  entries : Array Entry

private structure ReferenceLayout where
  offsets : Array Nat
  sourceOrder : Array Nat
  deriving Repr, DecidableEq

private structure NestedEntries where
  rows : Array (Array Entry)

private structure PackedEntries where
  offsets : Array Nat
  entries : Array Entry
  deriving Repr, DecidableEq

private structure Observation where
  firstSize : Nat
  secondSize : Nat
  thirdSize : Nat
  checksum : UInt64
  deriving Repr, DecidableEq

private structure Timing where
  repetitions : Nat
  medianNanos : Nat
  minNanos : Nat
  maxNanos : Nat
  checksum : UInt64

@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

@[inline] private def entryAt (index bucket : Nat) : Entry :=
  { bucket
    first := index * 131 + bucket * 17
    second := mix (UInt64.ofNat index) (UInt64.ofNat bucket) }

private def allOneFixture : Fixture :=
  let count := 16_384
  { name := "all entries in one bucket"
    bucketCount := 1
    entries := Array.ofFn (n := count) fun index ↦ entryAt index.val 0 }

private def uniformFixture : Fixture :=
  let count := 65_536
  let buckets := 256
  { name := "uniform buckets"
    bucketCount := buckets
    entries := Array.ofFn (n := count) fun index ↦
      entryAt index.val (index.val % buckets) }

private def sparseFixture : Fixture :=
  let count := 4_096
  let buckets := 65_536
  { name := "buckets much greater than entries"
    bucketCount := buckets
    entries := Array.ofFn (n := count) fun index ↦
      entryAt index.val ((index.val * 8_191 + 97) % buckets) }

private def lowFanoutFixture (ratio : Nat) : Fixture :=
  let count := 16_384
  let buckets := count * ratio
  { name := s!"low fan-out crossover B/E={ratio}"
    bucketCount := buckets
    entries := Array.ofFn (n := count) fun index ↦
      let group := index.val / 3
      let within := index.val % 3
      let offset := if within = 0 then 0 else ratio
      entryAt index.val (group * (3 * ratio) + offset) }

private def limitsFor (fixture : Fixture) : StableBuckets.Limits :=
  { maxBuckets := fixture.bucketCount
    maxEntries := fixture.entries.size }

/-
The nested rows deliberately differ from `StableBuckets`' flat counting-sort implementation.
Each row is flattened in bucket order so exact output parity remains directly observable.
-/
@[noinline] private def referenceBuild (fixture : Fixture) : Option ReferenceLayout := Id.run do
  let mut rows : Array (Array Nat) := Array.replicate fixture.bucketCount #[]
  for source in [0:fixture.entries.size] do
    let some entry := fixture.entries[source]?
      | return none
    if fixture.bucketCount ≤ entry.bucket then
      return none
    let some row := rows[entry.bucket]?
      | return none
    rows := rows.set! entry.bucket (row.push source)
  let mut offsets := Array.emptyWithCapacity (fixture.bucketCount + 1)
  let mut sourceOrder := Array.emptyWithCapacity fixture.entries.size
  for row in rows do
    offsets := offsets.push sourceOrder.size
    for source in row do
      sourceOrder := sourceOrder.push source
  offsets := offsets.push sourceOrder.size
  return some { offsets, sourceOrder }

private def observeBuildArrays (offsets sourceOrder : Array Nat) : Observation := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat offsets.size)
  for offset in offsets do
    checksum := mix checksum (UInt64.ofNat offset)
  checksum := mix checksum (UInt64.ofNat sourceOrder.size)
  for source in sourceOrder do
    checksum := mix checksum (UInt64.ofNat source)
  return {
    firstSize := offsets.size
    secondSize := sourceOrder.size
    thirdSize := 0
    checksum
  }

@[noinline] private def observeStableBuild (fixture : Fixture) : Option Observation := do
  let layout ←
    (StableBuckets.build (limitsFor fixture) fixture.bucketCount fixture.entries
      (fun entry ↦ entry.bucket)).toOption
  return observeBuildArrays layout.offsets layout.sourceOrder

@[noinline] private def observeReferenceBuild (fixture : Fixture) : Option Observation := do
  let layout ← referenceBuild fixture
  return observeBuildArrays layout.offsets layout.sourceOrder

/-
This is Unary's former retention shape: the nested value rows remain the output. In particular,
the timed path never pays to flatten them into a second representation.
-/
@[noinline] private def nestedRetainedBuild (fixture : Fixture) : Option NestedEntries := Id.run do
  let mut rows : Array (Array Entry) := Array.replicate fixture.bucketCount #[]
  for entry in fixture.entries do
    if fixture.bucketCount ≤ entry.bucket then
      return none
    let some row := rows[entry.bucket]?
      | return none
    rows := rows.set! entry.bucket (row.push entry)
  return some ⟨rows⟩

/-
This is Unary's packed retention shape: source order is only an intermediate index, while offsets
and gathered values are retained as the result.
-/
@[noinline] private def stableRetainedBuild (fixture : Fixture) : Option PackedEntries := do
  let layout ←
    (StableBuckets.build (limitsFor fixture) fixture.bucketCount fixture.entries
      (fun entry ↦ entry.bucket)).toOption
  let entries ← (layout.gatherMap fixture.entries id).toOption
  return ⟨layout.offsets, entries⟩

private def flattenNested (nested : NestedEntries) (entryCount : Nat) : PackedEntries := Id.run do
  let mut offsets := Array.emptyWithCapacity (nested.rows.size + 1)
  let mut entries := Array.emptyWithCapacity entryCount
  for row in nested.rows do
    offsets := offsets.push entries.size
    for entry in row do
      entries := entries.push entry
  offsets := offsets.push entries.size
  return ⟨offsets, entries⟩

@[inline] private def mixEntry (checksum : UInt64) (entry : Entry) : UInt64 :=
  let withBucket := mix checksum (UInt64.ofNat entry.bucket)
  let withFirst := mix withBucket (UInt64.ofNat entry.first)
  mix withFirst entry.second

private def observeNestedEntries (nested : NestedEntries) : Observation := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat nested.rows.size)
  let mut entries := 0
  for row in nested.rows do
    checksum := mix checksum (UInt64.ofNat row.size)
    entries := entries + row.size
    for entry in row do
      checksum := mixEntry checksum entry
  return {
    firstSize := nested.rows.size + 1
    secondSize := entries
    thirdSize := 0
    checksum
  }

private def observePackedEntries (packed : PackedEntries) : Option Observation := Id.run do
  unless packed.offsets[0]? = some 0 do
    return none
  unless packed.offsets.back? = some packed.entries.size do
    return none
  let bucketCount := packed.offsets.size - 1
  let mut checksum := mix 0 (UInt64.ofNat bucketCount)
  let mut entries := 0
  for bucket in [0:bucketCount] do
    let some first := packed.offsets[bucket]?
      | return none
    let some stop := packed.offsets[bucket + 1]?
      | return none
    if stop < first || packed.entries.size < stop then
      return none
    checksum := mix checksum (UInt64.ofNat (stop - first))
    entries := entries + (stop - first)
    for index in [first:stop] do
      let some entry := packed.entries[index]?
        | return none
      checksum := mixEntry checksum entry
  return some {
    firstSize := packed.offsets.size
    secondSize := entries
    thirdSize := 0
    checksum
  }

@[noinline] private def observeNestedRetention (fixture : Fixture) : Option Observation := do
  let nested ← nestedRetainedBuild fixture
  return observeNestedEntries nested

@[noinline] private def observeStableRetention (fixture : Fixture) : Option Observation := do
  let packed ← stableRetainedBuild fixture
  observePackedEntries packed

private def requireBuildParity (fixture : Fixture) : IO Unit := do
  let stable ←
    match StableBuckets.build (limitsFor fixture) fixture.bucketCount fixture.entries
        (fun entry ↦ entry.bucket) with
    | .ok layout => pure layout
    | .error cause =>
        throw <| IO.userError s!"{fixture.name}: stable build failed: {repr cause}"
  let some reference := referenceBuild fixture
    | throw <| IO.userError s!"{fixture.name}: reference build failed"
  unless stable.bucketCount = fixture.bucketCount &&
      stable.entryCount = fixture.entries.size &&
      stable.offsets = reference.offsets && stable.sourceOrder = reference.sourceOrder do
    throw <| IO.userError s!"{fixture.name}: stable/reference layouts differ"

private def requireRetentionParity (fixture : Fixture) : IO Unit := do
  let some nested := nestedRetainedBuild fixture
    | throw <| IO.userError s!"{fixture.name}: nested retention build failed"
  let some packed := stableRetainedBuild fixture
    | throw <| IO.userError s!"{fixture.name}: packed retention build failed"
  let canonical := flattenNested nested fixture.entries.size
  unless nested.rows.size = fixture.bucketCount && canonical = packed do
    throw <| IO.userError s!"{fixture.name}: retained representations differ"
  let nestedObserved := observeNestedEntries nested
  let some packedObserved := observePackedEntries packed
    | throw <| IO.userError s!"{fixture.name}: packed retention observation failed"
  unless nestedObserved = packedObserved do
    throw <| IO.userError s!"{fixture.name}: bucket-major observations differ"

private def referenceGatherMap (layout : ReferenceLayout) (column : Array α)
    (project : α → β) : Option (Array β) := Id.run do
  if column.size != layout.sourceOrder.size then
    return none
  let mut output := Array.emptyWithCapacity column.size
  for source in layout.sourceOrder do
    let some value := column[source]?
      | return none
    output := output.push (project value)
  return some output

private def observeGatherArrays (first : Array Nat) (second : Array UInt64)
    (third : Array Nat) : Observation := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat first.size)
  for value in first do
    checksum := mix checksum (UInt64.ofNat value)
  checksum := mix checksum (UInt64.ofNat second.size)
  for value in second do
    checksum := mix checksum value
  checksum := mix checksum (UInt64.ofNat third.size)
  for value in third do
    checksum := mix checksum (UInt64.ofNat value)
  return {
    firstSize := first.size
    secondSize := second.size
    thirdSize := third.size
    checksum
  }

@[noinline] private def observeStableGather (layout : StableBuckets.Layout)
    (entries : Array Entry) : Option Observation := do
  let first ← (layout.gatherMap entries (fun entry ↦ entry.first)).toOption
  let second ← (layout.gatherMap entries (fun entry ↦ entry.second)).toOption
  let third ← (layout.gatherMap entries (fun entry ↦ entry.bucket)).toOption
  return observeGatherArrays first second third

@[noinline] private def observeReferenceGather (layout : ReferenceLayout)
    (entries : Array Entry) : Option Observation := do
  let first ← referenceGatherMap layout entries fun entry ↦ entry.first
  let second ← referenceGatherMap layout entries fun entry ↦ entry.second
  let third ← referenceGatherMap layout entries fun entry ↦ entry.bucket
  return observeGatherArrays first second third

private def requireGatherParity (fixture : Fixture) (stable : StableBuckets.Layout)
    (reference : ReferenceLayout) : IO Unit := do
  let some stableObserved := observeStableGather stable fixture.entries
    | throw <| IO.userError s!"{fixture.name}: stable gather failed"
  let some referenceObserved := observeReferenceGather reference fixture.entries
    | throw <| IO.userError s!"{fixture.name}: reference gather failed"
  unless stableObserved = referenceObserved do
    throw <| IO.userError s!"{fixture.name}: stable/reference gathered columns differ"

private def warmup (name : String) (run : Unit → Option Observation) : IO Observation := do
  let some first ← IO.lazyPure fun _ ↦ run ()
    | throw <| IO.userError s!"{name}: first warmup failed"
  let some second ← IO.lazyPure fun _ ↦ run ()
    | throw <| IO.userError s!"{name}: second warmup failed"
  unless second = first do
    throw <| IO.userError s!"{name}: observation changed between warmups"
  return first

private def sample (name : String) (repetitions : Nat) (expected : Observation)
    (run : Unit → Option Observation) : IO (Nat × UInt64) := do
  if repetitions = 0 then
    throw <| IO.userError s!"{name}: benchmark requires a positive batch size"
  let start ← IO.monoNanosNow
  let mut checksum := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    let some current ← IO.lazyPure fun _ ↦ run ()
      | throw <| IO.userError s!"{name}: timed run failed"
    unless current = expected do
      throw <| IO.userError s!"{name}: observation changed during timing"
    checksum := mix checksum current.checksum
  let stop ← IO.monoNanosNow
  return (stop - start, checksum)

private def calibrate (name : String) (expected : Observation)
    (run : Unit → Option Observation) : IO Nat := do
  let mut repetitions := 1
  for _ in [0:2] do
    let measured ← sample name repetitions expected run
    let elapsed := max measured.1 1
    repetitions := min 4_096 (max 1 ((repetitions * 25_000_000) / elapsed))
  return repetitions

private def sortNanos (input : Array Nat) : Array Nat := Id.run do
  let mut output := input
  for left in [0:output.size] do
    for right in [left + 1:output.size] do
      if output[right]! < output[left]! then
        let value := output[left]!
        output := (output.set! left output[right]!).set! right value
  return output

private def bench (name : String) (expected : Observation)
    (run : Unit → Option Observation) : IO Timing := do
  let repetitions ← calibrate name expected run
  let mut samples := Array.emptyWithCapacity 7
  let mut checksum := mix 0 7
  for _ in [0:7] do
    let measured ← sample name repetitions expected run
    samples := samples.push (measured.1 / repetitions)
    checksum := mix checksum measured.2
  let sorted := sortNanos samples
  return {
    repetitions
    medianNanos := sorted[3]!
    minNanos := sorted[0]!
    maxNanos := sorted[6]!
    checksum
  }

private def report (name : String) (entries : Nat) (timing : Timing) : IO Unit := do
  let seconds := Float.ofNat (max timing.medianNanos 1) / 1_000_000_000.0
  let throughput := Float.ofNat entries / seconds
  IO.println <| s!"{name}: repetitions={timing.repetitions} " ++
    s!"median={timing.medianNanos / 1_000} us " ++
    s!"range=[{timing.minNanos / 1_000}, {timing.maxNanos / 1_000}] us " ++
    s!"entries/s={throughput} chk={timing.checksum}"

private def runBuildFixture (fixture : Fixture) : IO Unit := do
  requireBuildParity fixture
  IO.println <| s!"--- {fixture.name}: buckets={fixture.bucketCount} " ++
    s!"entries={fixture.entries.size} ---"
  let referenceExpected ← warmup "nested reference build" fun _ ↦
    observeReferenceBuild fixture
  let referenceTiming ← bench "nested reference build" referenceExpected fun _ ↦
    observeReferenceBuild fixture
  report "nested reference build" fixture.entries.size referenceTiming
  let stableExpected ← warmup "stable packed build" fun _ ↦ observeStableBuild fixture
  let stableTiming ← bench "stable packed build" stableExpected fun _ ↦
    observeStableBuild fixture
  report "stable packed build" fixture.entries.size stableTiming
  IO.println s!"nested/stable ratio={
    Float.ofNat referenceTiming.medianNanos /
      Float.ofNat (max stableTiming.medianNanos 1)}x"

private def runRetentionFixture (fixture : Fixture) : IO Unit := do
  requireRetentionParity fixture
  IO.println <| s!"--- retained representations: {fixture.name}; " ++
    s!"buckets={fixture.bucketCount} entries={fixture.entries.size} ---"
  let nestedExpected ← warmup "retained nested value rows" fun _ ↦
    observeNestedRetention fixture
  let nestedTiming ← bench "retained nested value rows" nestedExpected fun _ ↦
    observeNestedRetention fixture
  report "retained nested value rows" fixture.entries.size nestedTiming
  let packedExpected ← warmup "retained packed values" fun _ ↦
    observeStableRetention fixture
  let packedTiming ← bench "retained packed values" packedExpected fun _ ↦
    observeStableRetention fixture
  report "retained packed values" fixture.entries.size packedTiming
  IO.println s!"nested/packed retained ratio={
    Float.ofNat nestedTiming.medianNanos /
      Float.ofNat (max packedTiming.medianNanos 1)}x"

private def runGatherFixture (fixture : Fixture) : IO Unit := do
  let stable ←
    match StableBuckets.build (limitsFor fixture) fixture.bucketCount fixture.entries
        (fun entry ↦ entry.bucket) with
    | .ok layout => pure layout
    | .error cause =>
        throw <| IO.userError s!"{fixture.name}: stable gather setup failed: {repr cause}"
  let some reference := referenceBuild fixture
    | throw <| IO.userError s!"{fixture.name}: reference gather setup failed"
  requireGatherParity fixture stable reference
  IO.println <| s!"--- three-column gather: buckets={fixture.bucketCount} " ++
    s!"entries={fixture.entries.size}; layout construction excluded ---"
  let referenceExpected ← warmup "reference source-order gather x3" fun _ ↦
    observeReferenceGather reference fixture.entries
  let referenceTiming ← bench "reference source-order gather x3" referenceExpected fun _ ↦
    observeReferenceGather reference fixture.entries
  report "reference source-order gather x3" fixture.entries.size referenceTiming
  let stableExpected ← warmup "Layout.gatherMap x3" fun _ ↦
    observeStableGather stable fixture.entries
  let stableTiming ← bench "Layout.gatherMap x3" stableExpected fun _ ↦
    observeStableGather stable fixture.entries
  report "Layout.gatherMap x3" fixture.entries.size stableTiming
  IO.println s!"reference/stable gather ratio={
    Float.ofNat referenceTiming.medianNanos /
      Float.ofNat (max stableTiming.medianNanos 1)}x"

/-- Run skewed, crossover, retention, and reusable multi-column projection lanes. -/
def main : IO Unit := do
  let allOne := allOneFixture
  let uniform := uniformFixture
  let sparse := sparseFixture
  runBuildFixture allOne
  runBuildFixture uniform
  runBuildFixture sparse
  for ratio in #[1, 2, 4, 8] do
    runBuildFixture (lowFanoutFixture ratio)
  runRetentionFixture allOne
  runRetentionFixture uniform
  runRetentionFixture sparse
  runGatherFixture uniform

end StableBucketsBenchmark

def main : IO Unit := StableBucketsBenchmark.main
