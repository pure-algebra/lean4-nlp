import Nlp.Normalize.Numeric

/-!
# Exact numeric-normalization benchmark

This native benchmark measures checked longest-leftmost extraction over two four-times-separated
token counts. Fixtures are built before timing, complete proof-carrying results are consumed into
a stable checksum, and every timed output must equal the warmup observation.
-/

namespace NumericBenchmark

open Nlp.Normalize.Numeric

/-- Complete observable output accounting for one normalization run. -/
private structure Observation where
  mentions : Nat
  checksum : UInt64
  deriving Repr, DecidableEq

/-- Calibrated per-run timing summary. -/
private structure Timing where
  repetitions : Nat
  medianNanos : Nat
  minNanos : Nat
  maxNanos : Nat
  checksum : UInt64

/-- One materialized token-column lane. -/
private structure Fixture where
  name : String
  forms : Array String
  expectedMentions : Nat

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Consume every public mention coordinate, class, and exact rational component. -/
private def observe (result : Result) : Observation := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat result.source.size)
  checksum := mix checksum (UInt64.ofNat result.ranges.size)
  for mention in result.mentions do
    checksum := mix checksum (UInt64.ofNat mention.start)
    checksum := mix checksum (UInt64.ofNat mention.stop)
    checksum := mix checksum (if mention.kind == .cardinal then 0 else 1)
    checksum := mix checksum (hash mention.value.rational.num)
    checksum := mix checksum (UInt64.ofNat mention.value.rational.den)
  return ⟨result.mentions.size, checksum⟩

/-- Run the complete checked range normalizer. -/
@[noinline] private def run (fixture : Fixture) : Except Error Observation :=
  (normalizeRange fixture.forms 0 fixture.forms.size).map observe

/-- Build repeated word-cardinal and digit-ordinal phrases separated by nonnumeric tokens. -/
private def fixture (groups : Nat) : Fixture := Id.run do
  let mut forms := Array.emptyWithCapacity (groups * 7)
  for _ in [0:groups] do
    forms := forms.push "one"
    forms := forms.push "hundred"
    forms := forms.push "twenty"
    forms := forms.push "three"
    forms := forms.push "cats"
    forms := forms.push "21st"
    forms := forms.push "+1,234.50e-2"
  return ⟨s!"mixed exact numbers ({groups} groups)", forms, groups * 3⟩

/-- Establish exact deterministic output before timing begins. -/
private def warmup (fixture : Fixture) : IO Observation := do
  let first ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"numeric warmup failed: {repr cause}"
  unless first.mentions = fixture.expectedMentions do
    throw <| IO.userError s!"{fixture.name} produced {first.mentions} mentions"
  let second ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"numeric warmup failed: {repr cause}"
  unless second = first do
    throw <| IO.userError s!"{fixture.name} changed between warmups"
  return first

/-- Time a positive batch while comparing every result to the warmup observation. -/
private def sample (repetitions : Nat) (fixture : Fixture)
    (expected : Observation) : IO (Nat × UInt64) := do
  if repetitions = 0 then
    throw <| IO.userError "numeric benchmark requires a positive batch size"
  let start ← IO.monoNanosNow
  let mut checksum := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .error cause => throw <| IO.userError s!"numeric timed run failed: {repr cause}"
    | .ok current =>
        unless current = expected do
          throw <| IO.userError s!"{fixture.name} changed during timing"
        checksum := mix checksum current.checksum
  let stop ← IO.monoNanosNow
  return (stop - start, checksum)

/-- Calibrate twice toward one 25 ms batch. -/
private def calibrate (fixture : Fixture) (expected : Observation) : IO Nat := do
  let mut repetitions := 1
  for _ in [0:2] do
    let measured ← sample repetitions fixture expected
    let elapsed := max measured.1 1
    repetitions := min 4096 (max 1 ((repetitions * 25_000_000) / elapsed))
  return repetitions

/-- Sort the fixed seven-sample timing array. -/
private def sortNanos (input : Array Nat) : Array Nat := Id.run do
  let mut output := input
  for left in [0:output.size] do
    for right in [left + 1:output.size] do
      if output[right]! < output[left]! then
        let leftValue := output[left]!
        output := (output.set! left output[right]!).set! right leftValue
  return output

/-- Collect a seven-sample median and range. -/
private def bench (fixture : Fixture) (expected : Observation) : IO Timing := do
  let repetitions ← calibrate fixture expected
  let mut samples := Array.emptyWithCapacity 7
  let mut checksum := mix 0 7
  for _ in [0:7] do
    let measured ← sample repetitions fixture expected
    samples := samples.push (measured.1 / repetitions)
    checksum := mix checksum measured.2
  let sorted := sortNanos samples
  return ⟨repetitions, sorted[3]!, sorted[0]!, sorted[6]!, checksum⟩

/-- Validate, time, and report one lane. -/
private def runFixture (fixture : Fixture) : IO Unit := do
  let expected ← warmup fixture
  let timing ← bench fixture expected
  let seconds := Float.ofNat (max timing.medianNanos 1) / 1_000_000_000.0
  let throughput := Float.ofNat fixture.forms.size / seconds
  IO.println <| s!"{fixture.name}: tokens={fixture.forms.size} " ++
    s!"mentions={expected.mentions} repetitions={timing.repetitions} " ++
    s!"median={timing.medianNanos / 1000} us " ++
    s!"range=[{timing.minNanos / 1000}, {timing.maxNanos / 1000}] us " ++
    s!"tokens/s={throughput} chk={timing.checksum}"

/-- Run two scales whose token counts differ by exactly four. -/
def main : IO Unit := do
  runFixture (fixture 682)
  runFixture (fixture 2728)

end NumericBenchmark

def main : IO Unit := NumericBenchmark.main
