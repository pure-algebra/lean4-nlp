import Nlp.Pattern.TokenRegex

/-!
# Textual TokensRegex front-end benchmark

This native benchmark measures iterative scanning/lowering and end-to-end Thompson compilation on
two flat alternation sources whose term counts differ by four. Fixtures are built before timing,
every timed result must equal its warmup observation, and no machine-specific threshold is
asserted.
-/

namespace TokenRegexBenchmark

open Nlp.Pattern.TokenRegex

private structure Fixture where
  name : String
  terms : Nat
  source : String
  expectedNodes : Nat

private structure Observation where
  sourceBytes : Nat
  expandedNodes : Nat
  requiredLayers : Nat
  states : Nat
  edges : Nat
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

private def patternSource (terms : Nat) : String :=
  String.intercalate " | " <| (List.range terms).map fun index ↦
    s!"[word:token-{index % 64}]"

private def fixture (terms : Nat) : Fixture :=
  { name := s!"flat alternation ({terms} terms)"
    terms
    source := patternSource terms
    expectedNodes := 2 * terms - 1 }

@[noinline] private def observeParse (fixture : Fixture) : Option Observation := do
  let parsed ← (parse fixture.source).toOption
  let mut checksum := mix 0 (UInt64.ofNat parsed.source.utf8ByteSize)
  checksum := mix checksum (UInt64.ofNat parsed.expandedNodeCount)
  checksum := mix checksum (UInt64.ofNat parsed.requiredLayers.length)
  return ⟨parsed.source.utf8ByteSize, parsed.expandedNodeCount,
    parsed.requiredLayers.length, 0, 0, checksum⟩

@[noinline] private def observeCompile (fixture : Fixture) : Option Observation := do
  let compiled ← (compile fixture.source).toOption
  let mut checksum := mix 0 (UInt64.ofNat compiled.source.utf8ByteSize)
  checksum := mix checksum (UInt64.ofNat compiled.pattern.expandedNodeCount)
  checksum := mix checksum (UInt64.ofNat compiled.requiredLayers.length)
  checksum := mix checksum (UInt64.ofNat compiled.automaton.stateCount)
  checksum := mix checksum (UInt64.ofNat compiled.automaton.edgeCount)
  return ⟨compiled.source.utf8ByteSize, compiled.pattern.expandedNodeCount,
    compiled.requiredLayers.length, compiled.automaton.stateCount,
    compiled.automaton.edgeCount, checksum⟩

private def warmup (name : String) (fixture : Fixture)
    (run : Fixture → Option Observation) : IO Observation := do
  let some first ← IO.lazyPure fun _ ↦ run fixture
    | throw <| IO.userError s!"{name} warmup failed"
  unless first.expandedNodes == fixture.expectedNodes do
    throw <| IO.userError <| s!"{name} charged {first.expandedNodes} nodes; " ++
      s!"expected {fixture.expectedNodes}"
  let some second ← IO.lazyPure fun _ ↦ run fixture
    | throw <| IO.userError s!"{name} second warmup failed"
  unless second = first do
    throw <| IO.userError s!"{name} observation changed between warmups"
  return first

private def sample (name : String) (repetitions : Nat) (fixture : Fixture)
    (expected : Observation) (run : Fixture → Option Observation) : IO (Nat × UInt64) := do
  let start ← IO.monoNanosNow
  let mut checksum := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    let some current ← IO.lazyPure fun _ ↦ run fixture
      | throw <| IO.userError s!"{name} timed run failed"
    unless current = expected do
      throw <| IO.userError s!"{name} observation changed during timing"
    checksum := mix checksum current.checksum
  let stop ← IO.monoNanosNow
  return (stop - start, checksum)

private def calibrate (name : String) (fixture : Fixture) (expected : Observation)
    (run : Fixture → Option Observation) : IO Nat := do
  let mut repetitions := 1
  for _ in [0:2] do
    let measured ← sample name repetitions fixture expected run
    let elapsed := max measured.1 1
    repetitions := min 256 (max 1 ((repetitions * 20_000_000) / elapsed))
  return repetitions

private def sortNanos (input : Array Nat) : Array Nat := Id.run do
  let mut output := input
  for left in [0:output.size] do
    for right in [left + 1:output.size] do
      if output[right]! < output[left]! then
        let value := output[left]!
        output := (output.set! left output[right]!).set! right value
  return output

private def bench (name : String) (fixture : Fixture) (expected : Observation)
    (run : Fixture → Option Observation) : IO Timing := do
  let repetitions ← calibrate name fixture expected run
  let mut samples := Array.emptyWithCapacity 7
  let mut checksum := mix 0 7
  for _ in [0:7] do
    let measured ← sample name repetitions fixture expected run
    samples := samples.push (measured.1 / repetitions)
    checksum := mix checksum measured.2
  let sorted := sortNanos samples
  return ⟨repetitions, sorted[3]!, sorted[0]!, sorted[6]!, checksum⟩

private def report (name : String) (fixture : Fixture) (expected : Observation)
    (timing : Timing) : IO Unit := do
  let seconds := Float.ofNat (max timing.medianNanos 1) / 1_000_000_000.0
  let termThroughput := Float.ofNat fixture.terms / seconds
  let byteThroughput := Float.ofNat expected.sourceBytes / seconds
  IO.println <| s!"{name}: terms={fixture.terms} bytes={expected.sourceBytes} " ++
    s!"nodes={expected.expandedNodes} states={expected.states} edges={expected.edges} " ++
    s!"repetitions={timing.repetitions} median={timing.medianNanos / 1000} us " ++
    s!"range=[{timing.minNanos / 1000}, {timing.maxNanos / 1000}] us " ++
    s!"terms/s={termThroughput} bytes/s={byteThroughput} chk={timing.checksum}"

private def runFixture (fixture : Fixture) : IO Unit := do
  IO.println s!"--- {fixture.name} ---"
  let parsed ← warmup "parse" fixture observeParse
  let parseTiming ← bench "parse" fixture parsed observeParse
  report "parse" fixture parsed parseTiming
  let compiled ← warmup "compile" fixture observeCompile
  let compileTiming ← bench "compile" fixture compiled observeCompile
  report "parse + Thompson compile" fixture compiled compileTiming

/-- Run two source scales with an exact four-times term ratio. -/
def main : IO Unit := do
  runFixture (fixture 1_024)
  runFixture (fixture 4_096)

end TokenRegexBenchmark

def main : IO Unit := TokenRegexBenchmark.main
