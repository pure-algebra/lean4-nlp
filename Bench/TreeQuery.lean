import Nlp.Pattern.Tree

/-!
# Typed constituency-tree query benchmark

This native benchmark measures checked arena construction, typed query compilation, optimized
evaluation, and the shared independent denotation table on two four-times-separated deep trees.
Every public matching node contributes to a stable checksum and timed outputs must equal warmup.
-/

namespace TreeQueryBenchmark

open Nlp Nlp.Syntax Nlp.Pattern.TreeQuery

/-- One materialized named tree and its exact expected output accounting. -/
private structure Fixture where
  name : String
  tree : NamedTree
  nodes : Nat
  expectedMatches : Nat

/-- Complete observable output accounting for one checked tree-query run. -/
private structure Observation where
  nodes : Nat
  matchesFound : Nat
  work : Nat
  paths : Nat
  comparedBytes : Nat
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

/-- A relation-heavy query whose answer contains every strict ancestor of the terminal. -/
private def query : Query := .descendant (.label "leaf")

/-- Consume every public match coordinate and exact resource counter. -/
private def observe (arena : TreeArena) (result : Result arena query {}) : Observation := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat arena.nodeCount)
  checksum := mix checksum (UInt64.ofNat result.work)
  checksum := mix checksum (UInt64.ofNat result.paths)
  checksum := mix checksum (UInt64.ofNat result.comparedBytes)
  for matched in result.items do
    checksum := mix checksum (UInt64.ofNat matched.node)
    checksum := mix checksum (if matched.certificate.accepts matched.node then 1 else 0)
  return ⟨arena.nodeCount, result.items.size, result.work, result.paths,
    result.comparedBytes, checksum⟩

/-- Run arena construction, both query compilers/evaluators, and certified result sealing. -/
@[noinline] private def run (fixture : Fixture) :
    Except (TreeArenaError ⊕ CompileError ⊕ SearchError) Observation := do
  let built ← (TreeArena.buildNamedTree fixture.tree).mapError Sum.inl
  let compiled ← (compile query).mapError (Sum.inr ∘ Sum.inl)
  let result ← (findAll built.arena compiled).mapError (Sum.inr ∘ Sum.inr)
  return observe built.arena result

/-- Build a deep unary tree iteratively so construction does not recurse in the fixture builder. -/
private def fixture (nodes : Nat) : Fixture := Id.run do
  let mut tree : NamedTree := .leaf "leaf"
  for _ in [0:nodes - 1] do
    tree := .node "X" tree #[]
  return ⟨s!"descendant query over {nodes}-node unary tree", tree, nodes, nodes - 1⟩

/-- Establish exact deterministic output before timing begins. -/
private def warmup (fixture : Fixture) : IO Observation := do
  let first ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"tree-query warmup failed: {repr cause}"
  unless first.nodes = fixture.nodes && first.matchesFound = fixture.expectedMatches do
    throw <| IO.userError s!"{fixture.name} produced unexpected output accounting"
  let second ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"tree-query warmup failed: {repr cause}"
  unless second = first do
    throw <| IO.userError s!"{fixture.name} changed between warmups"
  return first

/-- Time a positive batch while comparing every result to the warmup observation. -/
private def sample (repetitions : Nat) (fixture : Fixture)
    (expected : Observation) : IO (Nat × UInt64) := do
  if repetitions = 0 then
    throw <| IO.userError "tree-query benchmark requires a positive batch size"
  let start ← IO.monoNanosNow
  let mut checksum := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .error cause => throw <| IO.userError s!"tree-query timed run failed: {repr cause}"
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

/-- Validate, time, and report one complete tree-query lane. -/
private def runFixture (fixture : Fixture) : IO Unit := do
  let expected ← warmup fixture
  let timing ← bench fixture expected
  let seconds := Float.ofNat (max timing.medianNanos 1) / 1_000_000_000.0
  let throughput := Float.ofNat fixture.nodes / seconds
  IO.println <| s!"{fixture.name}: nodes={fixture.nodes} " ++
    s!"matches={expected.matchesFound} repetitions={timing.repetitions} " ++
    s!"median={timing.medianNanos / 1000} us " ++
    s!"range=[{timing.minNanos / 1000}, {timing.maxNanos / 1000}] us " ++
    s!"nodes/s={throughput} chk={timing.checksum}"

/-- Run two exact node counts separated by a factor of four. -/
def main : IO Unit := do
  runFixture (fixture 4096)
  runFixture (fixture 16384)

end TreeQueryBenchmark

def main : IO Unit := TreeQueryBenchmark.main
