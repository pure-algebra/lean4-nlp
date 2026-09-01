import Nlp.Pipeline.Viterbi

/-!
# Constituency sentence-range benchmark

This native benchmark compares the legacy per-sentence `Array.extract` path with the compiled
Viterbi range API over the same concatenated documents. Every derivation is fully consumed and
the two paths must agree exactly before timing. No machine-specific performance threshold is
asserted.
-/

namespace ConstituencyBenchmark

open Nlp

/-- One sentence-length class with a calibrated document size and timed repetition count. -/
private structure Lane where
  /-- Human-readable lane label. -/
  name : String
  /-- Number of terminals in every sentence. -/
  sentenceLength : Nat
  /-- Number of sentences parsed by one observation. -/
  sentenceCount : Nat
  /-- Timed repetitions after equally many untimed warm-ups. -/
  repetitions : Nat

/-- One concatenated token column and its aligned sentence ranges. -/
private structure Fixture where
  words : Array Tok
  ranges : Array (Nat × Nat)

/-- Average elapsed time and a forced output checksum. -/
private structure Timing where
  nanos : Nat
  checksum : UInt64

/-- Checked parse outcome retained until the benchmark turns failures into readable errors. -/
private abbrev Observation :=
  Except ViterbiDerivationError (Option UInt64)

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Tiny ambiguous grammar that accepts every nonempty sequence of terminal zero. -/
private def grammar : CNF Vit :=
  { bin := #[⟨0, 0, 0, 1⟩]
    lex := #[⟨0, 0, 1⟩]
    start := 0
    nNT := 1 }

/-- Build one concatenated document fixture outside every timed region. -/
private def buildFixture (lane : Lane) : Fixture := Id.run do
  let total := lane.sentenceLength * lane.sentenceCount
  let words := Array.replicate total (0 : Tok)
  let mut ranges := Array.emptyWithCapacity lane.sentenceCount
  for sentence in [0:lane.sentenceCount] do
    let start := sentence * lane.sentenceLength
    ranges := ranges.push (start, start + lane.sentenceLength)
  return ⟨words, ranges⟩

/-- Consume every node and exact production/split coordinate in one derivation. -/
private def derivationChecksum : Parse.Viterbi.Derivation → UInt64
  | .lexical source lhs token =>
      mix (mix (mix 1 (UInt64.ofNat source)) lhs.toUInt64) token.toUInt64
  | .binary source lhs split left right =>
      let root := mix (mix (mix 2 (UInt64.ofNat source)) lhs.toUInt64)
        (UInt64.ofNat split)
      mix (mix root (derivationChecksum left)) (derivationChecksum right)

/-- Mix a sentence's exact fixture range and complete derivation into one observation. -/
@[inline] private def mixDerivation (checksum : UInt64) (start stop : Nat)
    (derivation : Parse.Viterbi.Derivation) : UInt64 :=
  let ranged := mix (mix checksum (UInt64.ofNat start)) (UInt64.ofNat stop)
  mix ranged (derivationChecksum derivation)

/-- Parse every materialized slice through the checked full-array entrypoint. -/
@[noinline] private def observeSlices (salt : UInt64) (model : ViterbiModel)
    (fixture : Fixture) : Observation := do
  let mut checksum := mix 0 salt
  for (start, stop) in fixture.ranges do
    let sentence := fixture.words.extract start stop
    match ← model.derivationRangeChecked? sentence 0 sentence.size with
    | none => return none
    | some derivation => checksum := mixDerivation checksum start stop derivation
  return some checksum

/-- Parse every normalized range through the checked zero-slice entrypoint. -/
@[noinline] private def observeRanges (salt : UInt64) (model : ViterbiModel)
    (fixture : Fixture) : Observation := do
  let mut checksum := mix 0 salt
  for (start, stop) in fixture.ranges do
    match ← model.derivationRangeChecked? fixture.words start stop with
    | none => return none
    | some derivation => checksum := mixDerivation checksum start stop derivation
  return some checksum

/-- Require a successful complete observation and expose checked failures distinctly. -/
private def requireObservation (name : String) : Observation → IO UInt64
  | .ok (some checksum) => pure checksum
  | .ok none => throw <| IO.userError s!"{name} did not parse"
  | .error cause => throw <| IO.userError s!"{name} invariant failure: {repr cause}"

/-- Warm up, time one exact observation path, and reject instability. -/
private def benchPath (name : String) (repetitions : Nat)
    (run : UInt64 → Observation) : IO Timing := do
  let mut expected := Array.emptyWithCapacity repetitions
  for index in [0:repetitions] do
    let salt := UInt64.ofNat (index + 1)
    let checksum ← requireObservation s!"{name} warm-up" <|
      ← IO.lazyPure fun _ ↦ run salt
    expected := expected.push checksum
  let start ← IO.monoNanosNow
  let mut aggregate := mix 0 (UInt64.ofNat repetitions)
  for index in [0:repetitions] do
    let salt := UInt64.ofNat (index + 1)
    let checksum ← requireObservation s!"{name} timed run" <|
      ← IO.lazyPure fun _ ↦ run salt
    if checksum != expected[index]! then
      throw <| IO.userError s!"{name} observation changed"
    aggregate := mix aggregate checksum
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Report one benchmark path in wall time and document-token throughput. -/
private def report (name : String) (tokens nanos : Nat) (checksum : UInt64) : IO Unit := do
  let seconds := Float.ofNat (max nanos 1) / 1000000000.0
  let throughput := Float.ofNat tokens / seconds
  IO.println <| s!"{name}: elapsed={nanos / 1000} us " ++
    s!"tokens/s={throughput} chk={checksum}"

/-- Check exact parity, then benchmark one sentence-length class. -/
private def benchLane (model : ViterbiModel) (lane : Lane) : IO Unit := do
  let fixture := buildFixture lane
  let tokens := lane.sentenceLength * lane.sentenceCount
  unless fixture.words.size == tokens && fixture.ranges.size == lane.sentenceCount do
    throw <| IO.userError s!"{lane.name} fixture shape changed"
  let sliced ← requireObservation s!"{lane.name} slice parity" <|
    ← IO.lazyPure fun _ ↦ observeSlices 0 model fixture
  let ranged ← requireObservation s!"{lane.name} range parity" <|
    ← IO.lazyPure fun _ ↦ observeRanges 0 model fixture
  if sliced != ranged then
    throw <| IO.userError s!"{lane.name} parity differs: slice={sliced}, range={ranged}"
  IO.println <| s!"--- {lane.name}: sentences={lane.sentenceCount} " ++
    s!"sentenceLength={lane.sentenceLength} tokens={tokens} " ++
    s!"repetitions={lane.repetitions} ---"
  let sliceTiming ← benchPath "materialized sentence slices" lane.repetitions fun salt ↦
    observeSlices salt model fixture
  report "Array.extract + compiled Viterbi" tokens sliceTiming.nanos sliceTiming.checksum
  let rangeTiming ← benchPath "zero-slice sentence ranges" lane.repetitions fun salt ↦
    observeRanges salt model fixture
  report "compiled Viterbi ranges" tokens rangeTiming.nanos rangeTiming.checksum
  if sliceTiming.checksum != rangeTiming.checksum then
    throw <| IO.userError s!"{lane.name} timed aggregate checksums differ"
  IO.println s!"range/slice speedup={
    Float.ofNat sliceTiming.nanos / Float.ofNat (max rangeTiming.nanos 1)}x"

/-- Run allocation-dominant short lanes through a length-32 CKY-dominant control. -/
def main : IO Unit := do
  let model ←
    match ViterbiModel.compile grammar with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"benchmark grammar failed: {repr cause}"
  let lanes : Array Lane :=
    #[⟨"length-1", 1, 4096, 6⟩, ⟨"length-2", 2, 2048, 6⟩,
      ⟨"length-4", 4, 512, 6⟩, ⟨"length-8", 8, 128, 5⟩,
      ⟨"length-16", 16, 32, 4⟩, ⟨"length-32 CKY control", 32, 4, 3⟩]
  for lane in lanes do
    benchLane model lane

end ConstituencyBenchmark

def main : IO Unit := ConstituencyBenchmark.main
