import Nlp.Dependency.Arborescence

/-!
# Nonprojective arborescence benchmark

This standalone benchmark consumes complete checked outputs from the dense single-root
Chu--Liu--Edmonds kernel. It covers dense dyadic scores, wide exponent spans, root-heavy ties,
sparse acyclic input, and the nested-cycle contraction adversary. Score compilation stays outside
every timed region.

Timings have no machine-specific threshold. Five materially sized batches report the median and
range. Every repetition must reproduce the same complete heads, relations, root count, exact
dyadic objective, optional Float report, and checksum before its duration is reported.
-/

namespace ArborescenceBenchmark

open Nlp Nlp.Dependency

/-- Fully consumed public output from one kernel run. -/
private structure Observation where
  analysed : Bool
  heads : Nat
  roots : Nat
  exactCost : Dyadic
  reportedCostBits : Option UInt64
  checksum : UInt64
  deriving DecidableEq

/-- Median per-run duration, sample range, and checksum across every timed batch. -/
private structure Timing where
  repetitions : Nat
  medianNanos : Nat
  minNanos : Nat
  maxNanos : Nat
  aggregate : UInt64

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Compile a two-relation fixture or retain its checked setup failure. -/
private def requireScores (n : Nat) (score : ArcScores.Scorer) : IO ArcScores :=
  match ArcScores.compileScorer n #["root", "dep"] 0 score with
  | .ok arcs => pure arcs
  | .error cause =>
      throw <| IO.userError s!"arborescence score compilation failed: {repr cause}"

/-- Consume every selected source coordinate and exact operational cost bit. -/
@[noinline] private def observe (arcs : ArcScores) : Except Arborescence.KernelError Observation :=
  match Arborescence.parse? arcs with
  | .error cause => .error cause
  | .ok none => .ok ⟨false, 0, 0, 0, none, mix 0 (UInt64.ofNat arcs.n)⟩
  | .ok (some result) => Id.run do
      let mut checksum := mix 0 (UInt64.ofNat result.heads.size)
      for head in result.heads do
        checksum := mix checksum (UInt64.ofNat head)
      checksum := mix checksum (UInt64.ofNat result.relations.size)
      for relation in result.relations do
        checksum := mix checksum relation.toUInt64
      match result.exactCost with
      | .zero => checksum := mix checksum 0
      | .ofOdd coefficient precision _ =>
          checksum := mix checksum 1
          checksum := mix checksum (UInt64.ofNat coefficient.natAbs)
          checksum := mix checksum (if precision < 0 then 1 else 0)
          checksum := mix checksum (UInt64.ofNat precision.natAbs)
      let reportedCostBits := result.reportedCost?.map Float.toBits
      checksum := mix checksum (if reportedCostBits.isSome then 1 else 0)
      if let some bits := reportedCostBits then
        checksum := mix checksum bits
      return .ok ⟨true, result.heads.size, result.heads.count 0,
        result.exactCost, reportedCostBits, checksum⟩

/-- Require one stable warmup observation with the advertised analysis outcome. -/
private def requireObservation (arcs : ArcScores) (expectedAnalysis : Bool) : IO Observation := do
  match ← IO.lazyPure fun _ ↦ observe arcs with
  | .error cause => throw <| IO.userError s!"arborescence warmup failed: {repr cause}"
  | .ok value =>
      unless value.analysed = expectedAnalysis do
        throw <| IO.userError "arborescence warmup returned the wrong analysis outcome"
      if value.analysed && (value.heads != arcs.n || value.roots != 1) then
        throw <| IO.userError "arborescence warmup violated its checked output shape"
      return value

/-- Time one complete-output batch and reject any output instability. -/
private def sample (repetitions : Nat) (arcs : ArcScores)
    (expected : Observation) : IO (Nat × UInt64) := do
  let start ← IO.monoNanosNow
  let mut aggregate := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    match ← IO.lazyPure fun _ ↦ observe arcs with
    | .error cause => throw <| IO.userError s!"arborescence inference failed: {repr cause}"
    | .ok current =>
        unless current = expected do
          throw <| IO.userError "arborescence output changed between repetitions"
        aggregate := mix aggregate current.checksum
  let stop ← IO.monoNanosNow
  return ((stop - start) / repetitions, aggregate)

/-- Double a small starting count until one checked batch is long enough to measure credibly. -/
private def calibrateRepetitions (minimumBatchNanos initial : Nat) (arcs : ArcScores)
    (expected : Observation) : IO Nat := do
  let mut repetitions := max initial 1
  for _attempt in [0:16] do
    let (averageNanos, _checksum) ← sample repetitions arcs expected
    if minimumBatchNanos ≤ averageNanos * repetitions || 4096 ≤ repetitions then
      return repetitions
    repetitions := min 4096 (repetitions * 2)
  return repetitions

/-- Sort the small duration sample without introducing benchmark dependencies. -/
private def sortNanos (samples : Array Nat) : Array Nat := Id.run do
  let mut sorted := samples
  for leftIndex in [0:sorted.size] do
    for rightIndex in [leftIndex + 1:sorted.size] do
      let left := sorted.getD leftIndex 0
      let right := sorted.getD rightIndex 0
      if right < left then
        sorted := (sorted.set! leftIndex right).set! rightIndex left
  return sorted

/-- Time several batches and retain their median, range, and complete-output checksum. -/
private def bench (batches initialRepetitions : Nat) (arcs : ArcScores)
    (expected : Observation) : IO Timing := do
  if batches = 0 then
    throw <| IO.userError "arborescence benchmark requires a positive batch count"
  let repetitions ← calibrateRepetitions 25000000 initialRepetitions arcs expected
  let mut samples := Array.emptyWithCapacity batches
  let mut aggregate := mix 0 (UInt64.ofNat batches)
  for _batch in [0:batches] do
    let (nanos, checksum) ← sample repetitions arcs expected
    samples := samples.push nanos
    aggregate := mix aggregate checksum
  let sorted := sortNanos samples
  return ⟨repetitions, sorted.getD (sorted.size / 2) 0, sorted.getD 0 0,
    sorted.getD (sorted.size - 1) 0, aggregate⟩

/-- Report token and dense directed-candidate throughput for one complete-output lane. -/
private def report (name : String) (arcs : ArcScores) (timing : Timing) : IO Unit := do
  let seconds := Float.ofNat (max timing.medianNanos 1) / 1000000000.0
  let tokensPerSecond := Float.ofNat arcs.n / seconds
  let candidatesPerSecond := Float.ofNat (arcs.n * arcs.n) / seconds
  IO.println <| s!"{name}: n={arcs.n} workspace={Arborescence.workspaceEntryCountFor arcs} " ++
    s!"repetitions={timing.repetitions} " ++
    s!"median={timing.medianNanos / 1000} us " ++
    s!"range=[{timing.minNanos / 1000}, {timing.maxNanos / 1000}] us " ++
    s!"tokens/s={tokensPerSecond} " ++
    s!"candidates/s={candidatesPerSecond} chk={timing.aggregate}"

/-- Compile, warm, time, and report one deterministic benchmark fixture. -/
private def runFixture (name : String) (n repetitions : Nat)
    (expectedAnalysis : Bool) (score : ArcScores.Scorer) : IO Unit := do
  let arcs ← requireScores n score
  let expected ← requireObservation arcs expectedAnalysis
  let timing ← bench 5 repetitions arcs expected
  report name arcs timing

/-- Finite dyadic dense costs exercise the ordinary quadratic lane. -/
@[inline] private def denseScore (seed head dependent relation : Nat) : Float :=
  let numerator :=
    (head * 29 + dependent * 17 + relation * 11 + seed * 7 + head * dependent) % 257
  Float.ofNat numerator / 8.0

/-- One sparse chain reaches every token without requiring a contraction. -/
@[inline] private def chainScore (head dependent relation : Nat) : Float :=
  if head = 0 && dependent = 1 then
    0.0
  else if relation = 1 && 1 < dependent && head + 1 = dependent then
    1.0
  else
    inf

/-- Cheap artificial-root arcs force the symbolic one-root objective to dominate score. -/
@[inline] private def rootHeavyScore (head _dependent relation : Nat) : Float :=
  if head = 0 then 0.0 else if relation = 1 then 100.0 else inf

/-- Subnormal and ordinary arcs exercise variable-width exact integer comparisons. -/
@[inline] private def wideExponentScore (head dependent relation : Nat) : Float :=
  if head = 0 then
    1.0
  else if relation = 1 then
    if (head + dependent) % 2 = 0 then Float.ofBits 1 else 0.5
  else
    inf

/-- Nested contractions grow one two-component cycle at every merge. -/
@[inline] private def nestedCycleScore (n head dependent relation : Nat) : Float :=
  if head = 0 && dependent = 1 then
    1.0
  else if relation = 1 && dependent = 1 && 2 ≤ head && head ≤ n then
    0.0
  else if relation = 1 && 2 ≤ dependent && head = 1 then
    0.0
  else
    inf

/-- One final dependent has no incoming edge, so checked inference returns no analysis. -/
@[inline] private def disconnectedScore (n head dependent relation : Nat) : Float :=
  if dependent = n then inf else chainScore head dependent relation

/-- Run dense, constrained-root, sparse, nested-cycle, and absent-analysis lanes. -/
def main : IO Unit := do
  for fixture in #[(32, 1, 1), (64, 1, 2), (128, 1, 3), (256, 1, 4)] do
    let n := fixture.1
    let repetitions := fixture.2.1
    let seed := fixture.2.2
    runFixture s!"dense dyadic seed={seed}" n repetitions true (denseScore seed)
  runFixture "wide exponent span" 96 1 true wideExponentScore
  runFixture "root-heavy ties" 256 1 true rootHeavyScore
  runFixture "sparse chain" 512 1 true chainScore
  runFixture "nested contractions" 192 1 true (nestedCycleScore 192)
  runFixture "disconnected" 256 1 false (disconnectedScore 256)

end ArborescenceBenchmark

def main : IO Unit := ArborescenceBenchmark.main
