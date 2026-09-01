import Nlp.Dependency.Viterbi

/-!
# Projective dependency parsing benchmark

This standalone benchmark compares the boxed semiring-generic Eisner recurrence with the
unboxed labeled min-cost specialization and checked extraction. Every timed observation consumes
the complete chart. Specialized observations also consume every extracted head and relation.

Fixtures use finite dyadic costs, allowing exact IEEE-754 goal-bit comparison across the generic
and specialized recurrence shapes. Timings have no machine-specific threshold. Label selection
is compiled before ordinary parsing lanes and measured separately in a label-heavy lane.
-/

namespace DependencyBenchmark

open Nlp Nlp.Dependency

/-- Stable checksum and result metadata from the boxed generic recurrence. -/
private structure GenericObservation where
  goalBits : UInt64
  entries : Nat
  chartChecksum : UInt64
  deriving Repr, DecidableEq

/-- Stable checksum and result metadata from specialized inference and extraction. -/
private structure SpecializedObservation where
  goalBits : UInt64
  entries : Nat
  chartChecksum : UInt64
  treeChecksum : UInt64
  extracted : Bool
  deriving Repr, DecidableEq

/-- Stable checksum and footprint from one labeled-score compilation. -/
private structure CompileObservation where
  entries : Nat
  checksum : UInt64
  deriving Repr, DecidableEq

/-- Average wall time and an aggregate checksum that keeps all repetitions observable. -/
private structure Timing where
  nanos : Nat
  checksum : UInt64

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Ordered relation names with ordinal zero reserved for the artificial-root relation. -/
private def relationNames (count : Nat) : Array String :=
  Array.ofFn (n := count) fun relation ↦
    if relation.val = 0 then "root" else s!"rel{relation.val}"

/--
Finite dyadic labeled costs for deterministic parity and throughput fixtures.

`ArcScores` invokes relation zero only for artificial-root arcs and excludes it from real-token
arcs, so the same formula can remain total over all coordinates.
-/
@[inline] private def score (seed head dependent relation : Nat) : Float :=
  let numerator :=
    (head * 29 + dependent * 17 + relation * 11 + seed * 7 + head * dependent) % 97
  Float.ofNat numerator / 8.0

/-- Compile one finite benchmark fixture or raise a source-rich setup failure. -/
private def requireScores (n relations seed : Nat) : IO ArcScores :=
  match ArcScores.compileScorer n (relationNames relations) 0 (score seed) with
  | .ok arcs => pure arcs
  | .error cause =>
      throw <| IO.userError s!"dependency score compilation failed: {repr cause}"

/-- Consume every boxed cost in the generic chart and retain its exact goal bits. -/
@[noinline] private def observeGeneric (arcs : ArcScores) : GenericObservation :=
  let weights := arcs.toArcWeights
  let chart := Eisner.insideChart weights
  let goal := Eisner.goalFromChart weights chart
  let checksum := chart.values.foldl
    (fun state value ↦ mix state value.toFloat.toBits)
    (mix 0 (UInt64.ofNat chart.values.size))
  ⟨goal.toFloat.toBits, chart.values.size, checksum⟩

/-- Consume every specialized score, split, extracted head, and exact relation ordinal. -/
@[noinline] private def observeSpecialized (arcs : ArcScores) : SpecializedObservation := Id.run do
  let chart := Eisner.viterbi arcs
  let mut chartChecksum := mix 0 (UInt64.ofNat chart.score.size)
  for value in chart.score do
    chartChecksum := mix chartChecksum value.toBits
  chartChecksum := mix chartChecksum (UInt64.ofNat chart.split.size)
  for split in chart.split do
    chartChecksum := mix chartChecksum split.toUInt64
  chartChecksum := mix chartChecksum chart.root.toUInt64
  chartChecksum := mix chartChecksum chart.rootCost.toBits
  match Eisner.extract? arcs chart with
  | none =>
      return ⟨chart.rootCost.toBits, chart.score.size, chartChecksum, 0, false⟩
  | some result =>
      let mut treeChecksum := mix 0 (UInt64.ofNat result.heads.size)
      for head in result.heads do
        treeChecksum := mix treeChecksum (UInt64.ofNat head)
      treeChecksum := mix treeChecksum (UInt64.ofNat result.relations.size)
      for relation in result.relations do
        treeChecksum := mix treeChecksum relation.toUInt64
      treeChecksum := mix treeChecksum result.cost.toBits
      return ⟨chart.rootCost.toBits, chart.score.size, chartChecksum, treeChecksum, true⟩

/-- Consume all compact arc costs, relation ordinals, and relation names after compilation. -/
@[noinline] private def observeCompilation (arcs : ArcScores) : CompileObservation := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat arcs.n)
  checksum := mix checksum (UInt64.ofNat arcs.costs.size)
  for cost in arcs.costs do
    checksum := mix checksum cost.toBits
  checksum := mix checksum (UInt64.ofNat arcs.relations.size)
  for relation in arcs.relations do
    checksum := mix checksum relation.toUInt64
  checksum := mix checksum arcs.rootRelation.toUInt64
  for name in arcs.relationNames do
    checksum := mix checksum (UInt64.ofNat name.utf8ByteSize)
  return ⟨arcs.costs.size, checksum⟩

/-- Time fully consumed generic observations and reject any instability. -/
private def benchGeneric (repetitions : Nat) (arcs : ArcScores) : IO Timing := do
  let expected ← IO.lazyPure fun _ ↦ observeGeneric arcs
  let start ← IO.monoNanosNow
  let mut aggregate := expected.chartChecksum
  for _ in [0:repetitions] do
    let current ← IO.lazyPure fun _ ↦ observeGeneric arcs
    if current != expected then
      throw <| IO.userError "generic dependency observation changed"
    aggregate := mix aggregate current.chartChecksum
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Time specialized inference plus checked extraction and reject any instability. -/
private def benchSpecialized (repetitions : Nat) (arcs : ArcScores) : IO Timing := do
  let expected ← IO.lazyPure fun _ ↦ observeSpecialized arcs
  let start ← IO.monoNanosNow
  let mut aggregate := mix expected.chartChecksum expected.treeChecksum
  for _ in [0:repetitions] do
    let current ← IO.lazyPure fun _ ↦ observeSpecialized arcs
    if current != expected then
      throw <| IO.userError "specialized dependency observation changed"
    aggregate := mix aggregate current.chartChecksum
    aggregate := mix aggregate current.treeChecksum
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Compile and consume a label-heavy fixture repeatedly without entering the parser. -/
private def benchCompilation (repetitions n relations seed : Nat) : IO Timing := do
  let names := relationNames relations
  let run : Unit → Except ArcScoreError CompileObservation := fun _ ↦
    (ArcScores.compileScorer n names 0 (score seed)).map observeCompilation
  let expected ←
    match ← IO.lazyPure fun _ ↦ run () with
    | .ok value => pure value
    | .error cause =>
        throw <| IO.userError s!"label-heavy warmup failed: {repr cause}"
  let start ← IO.monoNanosNow
  let mut aggregate := expected.checksum
  for _ in [0:repetitions] do
    match ← IO.lazyPure fun _ ↦ run () with
    | .error cause =>
        throw <| IO.userError s!"label-heavy compilation failed: {repr cause}"
    | .ok current =>
        if current != expected then
          throw <| IO.userError "label-heavy dependency compilation changed"
        aggregate := mix aggregate current.checksum
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Report one parser lane in time and token throughput. -/
private def reportKernel (name : String) (tokens nanos : Nat) (checksum : UInt64) : IO Unit := do
  let seconds := Float.ofNat (max nanos 1) / 1000000000.0
  let throughput := Float.ofNat tokens / seconds
  IO.println s!"{name}: elapsed={nanos / 1000} us tokens/s={throughput} chk={checksum}"

/-- Compile, validate exact parity, and time one ordinary parsing fixture. -/
private def benchFixture (n relations seed repetitions : Nat) : IO Unit := do
  let arcs ← requireScores n relations seed
  let generic ← IO.lazyPure fun _ ↦ observeGeneric arcs
  let specialized ← IO.lazyPure fun _ ↦ observeSpecialized arcs
  let directGoal ← IO.lazyPure fun _ ↦ (Eisner.inside arcs.toArcWeights).toFloat.toBits
  let expectedEntries := Eisner.chartEntryCount n
  unless generic.goalBits == directGoal && generic.goalBits == specialized.goalBits do
    throw <| IO.userError s!"generic/specialized dependency goals differ at n={n}"
  unless generic.entries == expectedEntries && specialized.entries == expectedEntries do
    throw <| IO.userError s!"dependency chart footprint changed at n={n}"
  unless specialized.extracted do
    throw <| IO.userError s!"finite dependency fixture failed extraction at n={n}"
  let specializedAgain ← IO.lazyPure fun _ ↦ observeSpecialized arcs
  unless specializedAgain.treeChecksum == specialized.treeChecksum do
    throw <| IO.userError s!"dependency extraction is nondeterministic at n={n}"
  let visits := ArcScores.scoreVisitCount n relations
  IO.println <| s!"--- n={n} relations={relations} chartEntries={expectedEntries} " ++
    s!"labeledScoreVisits={visits} repetitions={repetitions} ---"
  let genericTiming ← benchGeneric repetitions arcs
  reportKernel "generic boxed inside" n genericTiming.nanos genericTiming.checksum
  let specializedTiming ← benchSpecialized repetitions arcs
  reportKernel "specialized viterbi+extract" n specializedTiming.nanos specializedTiming.checksum
  IO.println s!"specialized/generic speedup={
    Float.ofNat genericTiming.nanos / Float.ofNat (max specializedTiming.nanos 1)}x"

/-- Run parity-gated parser lanes and an isolated label-heavy compilation lane. -/
def main : IO Unit := do
  for fixture in #[(16, 8, 1, 8), (32, 8, 2, 5), (48, 8, 3, 3),
      (64, 8, 4, 2), (96, 8, 5, 1)] do
    benchFixture fixture.1 fixture.2.1 fixture.2.2.1 fixture.2.2.2

  let compileTokens := 64
  let compileRelations := 256
  let compileVisits := ArcScores.scoreVisitCount compileTokens compileRelations
  let compileTiming ← benchCompilation 3 compileTokens compileRelations 19
  let seconds := Float.ofNat (max compileTiming.nanos 1) / 1000000000.0
  let visitsPerSecond := Float.ofNat compileVisits / seconds
  IO.println <| s!"--- label-heavy compile: n={compileTokens} relations={compileRelations} " ++
    s!"arcEntries={ArcScores.entryCount compileTokens} scoreVisits={compileVisits} ---"
  IO.println <| s!"compile only: elapsed={compileTiming.nanos / 1000} us " ++
    s!"scoreVisits/s={visitsPerSecond} chk={compileTiming.checksum}"

end DependencyBenchmark

def main : IO Unit := DependencyBenchmark.main
