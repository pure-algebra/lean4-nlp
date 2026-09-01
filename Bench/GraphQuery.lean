import Nlp.Pattern.Graph

/-!
# Typed dependency-graph query benchmark

This native benchmark measures checked dual-index construction plus bounded query evaluation on
two four-times-separated chains. Fixtures are materialized before timing, every public match and
binding contributes to a stable checksum, and every timed output must equal the warmup result.
-/

namespace GraphQueryBenchmark

open Nlp.Dependency Nlp.Pattern Nlp.Pattern.GraphQuery

/-- One materialized checked dependency graph and its exact expected query output size. -/
private structure Fixture where
  name : String
  graph : Graph String
  checkedQuery : CheckedQuery {}
  expectedMatches : Nat

/-- Complete observable output accounting for one checked query run. -/
private structure Observation where
  nodes : Nat
  edges : Nat
  matchCount : Nat
  work : Nat
  states : Nat
  comparisonBytes : Nat
  checksum : UInt64
  deriving Repr, DecidableEq

/-- Calibrated per-run timing summary. -/
private structure Timing where
  repetitions : Nat
  medianNanos : Nat
  minNanos : Nat
  maxNanos : Nat
  checksum : UInt64

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Consume one graph node identifier without relying on textual rendering. -/
@[inline] private def mixNode (state : UInt64) : NodeId → UInt64
  | .root => mix state 0
  | .word index => mix (mix state 1) (UInt64.ofNat index)
  | .empty anchor copy =>
      mix (mix (mix state 2) (UInt64.ofNat anchor)) (UInt64.ofNat copy)
  | .copy index copy =>
      mix (mix (mix state 3) (UInt64.ofNat index)) (UInt64.ofNat copy)

/-- A direct-edge query retaining both endpoints for complete observable output. -/
private def query : Query :=
  .bind "head" <| .outgoing .any <| .bind "dependent" (.node .any)

/-- Consume every public anchor and named-node binding. -/
private def observe (index : Index) (result : Result index config) : Observation := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat index.nodeCount)
  checksum := mix checksum (UInt64.ofNat index.edgeCount)
  for matched in result.items do
    checksum := mixNode checksum matched.anchor
    checksum := mix checksum (UInt64.ofNat matched.bindings.size)
    for binding in matched.bindings do
      checksum := mix checksum (hash binding.name)
      checksum := mixNode checksum binding.node
  checksum := mix checksum (UInt64.ofNat result.work)
  checksum := mix checksum (UInt64.ofNat result.states)
  checksum := mix checksum (UInt64.ofNat result.comparisonBytes)
  return ⟨index.nodeCount, index.edgeCount, result.items.size, result.work, result.states,
    result.comparisonBytes, checksum⟩

/-- Run the complete checked graph-index and bounded-query path. -/
@[noinline] private def run (fixture : Fixture) :
    Except (IndexError ⊕ SearchError) Observation := do
  let index ← (Index.compileGraph fixture.graph).mapError Sum.inl
  let result ← (findAllCheckedWith index fixture.checkedQuery).mapError Sum.inr
  return observe index result

/-- Build a rooted dependency chain with one incoming arc per stored node. -/
private def chain (nodes : Nat) : Except (GraphError String) (Graph String) := Id.run do
  let mut rows : Array (Row String) := Array.emptyWithCapacity nodes
  for index in [0:nodes] do
    let dependent := index + 1
    let head := if dependent = 1 then .root else .word (dependent - 1)
    let relation := if dependent = 1 then "root" else "dep"
    rows := rows.push ⟨.word dependent, #[⟨head, relation, .basic⟩]⟩
  return Graph.ofRows rows

/-- Materialize one checked fixture before benchmark timing begins. -/
private def fixture (nodes : Nat) : Except (GraphError String ⊕ SearchError) Fixture := do
  let graph ← (chain nodes).mapError Sum.inl
  let checkedQuery ← query.check.mapError Sum.inr
  return ⟨s!"direct query over {nodes}-node chain", graph, checkedQuery, nodes⟩

/-- Establish exact deterministic output before timing begins. -/
private def warmup (fixture : Fixture) : IO Observation := do
  let first ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"graph-query warmup failed: {repr cause}"
  unless first.matchCount = fixture.expectedMatches do
    throw <| IO.userError s!"{fixture.name} produced {first.matchCount} matches"
  let second ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"graph-query warmup failed: {repr cause}"
  unless second = first do
    throw <| IO.userError s!"{fixture.name} changed between warmups"
  return first

/-- Time a positive batch while comparing every result to the warmup observation. -/
private def sample (repetitions : Nat) (fixture : Fixture)
    (expected : Observation) : IO (Nat × UInt64) := do
  if repetitions = 0 then
    throw <| IO.userError "graph-query benchmark requires a positive batch size"
  let start ← IO.monoNanosNow
  let mut checksum := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .error cause => throw <| IO.userError s!"graph-query timed run failed: {repr cause}"
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
        let value := output[left]!
        output := (output.set! left output[right]!).set! right value
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

/-- Validate, time, and report one checked graph-query lane. -/
private def runFixture (fixture : Fixture) : IO Unit := do
  let expected ← warmup fixture
  let timing ← bench fixture expected
  let seconds := Float.ofNat (max timing.medianNanos 1) / 1_000_000_000.0
  let throughput := Float.ofNat fixture.graph.nodeCount / seconds
  IO.println <| s!"{fixture.name}: nodes={fixture.graph.nodeCount} " ++
    s!"matches={expected.matchCount} repetitions={timing.repetitions} " ++
    s!"work={expected.work} states={expected.states} cmpBytes={expected.comparisonBytes} " ++
    s!"median={timing.medianNanos / 1000} us " ++
    s!"range=[{timing.minNanos / 1000}, {timing.maxNanos / 1000}] us " ++
    s!"nodes/s={throughput} chk={timing.checksum}"

/-- Run two scales whose graph sizes differ by exactly four. -/
def main : IO Unit := do
  let small ←
    match fixture 4096 with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"small graph fixture failed: {repr cause}"
  let large ←
    match fixture 16384 with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"large graph fixture failed: {repr cause}"
  runFixture small
  runFixture large

end GraphQueryBenchmark

def main : IO Unit := GraphQueryBenchmark.main
