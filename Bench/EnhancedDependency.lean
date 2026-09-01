import Nlp.Dependency.EnglishEnhanced

/-!
# English enhanced-dependency benchmark

This native benchmark measures the complete checked `enhanceArraysWith?` path. Fixtures are
materialized and validated before timing. Every repetition consumes and exactly compares every
CSR column and the rule-family counts, then contributes their stable checksum to the report.

The four lanes isolate a long identity tree, two nominal `case` fan-out scales, and broad
coordination nested through successive governors. Timings use calibrated batches near 25 ms and
report a seven-sample median and range without imposing a machine-specific threshold.
-/

namespace EnhancedDependencyBenchmark

open Nlp.Dependency
open Nlp.Dependency.EnglishEnhanced

/-- Materialized aligned columns and exact expected output accounting for one benchmark lane. -/
private structure Fixture where
  name : String
  heads : Array Nat
  relations : Array String
  forms : Array String
  lemmas : Array String
  pos : Array String
  config : Config
  expectedCounts : Counts

/-- Exact public output snapshot plus a checksum that consumes all retained graph storage. -/
private structure Observation where
  nodes : Array NodeId
  offsets : Array Nat
  heads : Array NodeId
  relations : Array String
  origins : Array Origin
  counts : Counts
  nodeCount : Nat
  edgeCount : Nat
  checksum : UInt64
  deriving DecidableEq

/-- Total batch duration and an observable checksum over all repetitions. -/
private structure Batch where
  elapsedNanos : Nat
  aggregate : UInt64

/-- Median per-run duration, sample range, calibrated batch size, and output checksum. -/
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

/-- Consume a complete string together with its exact UTF-8 width. -/
@[inline] private def mixString (state : UInt64) (value : String) : UInt64 :=
  mix (mix state (UInt64.ofNat value.utf8ByteSize)) (hash value)

/-- Consume every constructor and coordinate of a graph node identifier. -/
@[inline] private def mixNode (state : UInt64) : NodeId → UInt64
  | .root => mix state 0
  | .word index => mix (mix state 1) (UInt64.ofNat index)
  | .empty anchor copy =>
      mix (mix (mix state 2) (UInt64.ofNat anchor)) (UInt64.ofNat copy)
  | .copy index copy =>
      mix (mix (mix state 3) (UInt64.ofNat index)) (UInt64.ofNat copy)

/-- Stable constructor ordinal for enhanced-arc provenance. -/
@[inline] private def originCode : Origin → UInt64
  | .basic => 0
  | .enhanced => 1
  | .empty => 2
  | .copy => 3

/-- Consume every public CSR column, graph count, and enhancement-family count. -/
private def observe (result : Result) : Observation := Id.run do
  let graph := result.graph
  let mut checksum := mix 0 (UInt64.ofNat graph.nodes.size)
  for node in graph.nodes do
    checksum := mixNode checksum node
  checksum := mix checksum (UInt64.ofNat graph.offsets.size)
  for offset in graph.offsets do
    checksum := mix checksum (UInt64.ofNat offset)
  checksum := mix checksum (UInt64.ofNat graph.heads.size)
  for head in graph.heads do
    checksum := mixNode checksum head
  checksum := mix checksum (UInt64.ofNat graph.relations.size)
  for relation in graph.relations do
    checksum := mixString checksum relation
  checksum := mix checksum (UInt64.ofNat graph.origins.size)
  for origin in graph.origins do
    checksum := mix checksum (originCode origin)
  checksum := mix checksum (UInt64.ofNat result.counts.basic)
  checksum := mix checksum (UInt64.ofNat result.counts.lexicalized)
  checksum := mix checksum (UInt64.ofNat result.counts.propagated)
  checksum := mix checksum (UInt64.ofNat graph.nodeCount)
  checksum := mix checksum (UInt64.ofNat graph.edgeCount)
  return ⟨graph.nodes, graph.offsets, graph.heads, graph.relations, graph.origins,
    result.counts, graph.nodeCount, graph.edgeCount, checksum⟩

/-- Run the complete checked transformer and retain an exact observable snapshot. -/
@[noinline] private def run (fixture : Fixture) : Except Error Observation :=
  (enhanceArraysWith? fixture.config fixture.heads fixture.relations fixture.forms
    fixture.lemmas fixture.pos).map observe

/-- Construct a long single-root chain whose enhanced output is the basic graph itself. -/
private def identityFixture (tokens : Nat) : Fixture := Id.run do
  let mut heads := Array.emptyWithCapacity tokens
  let mut relations := Array.emptyWithCapacity tokens
  let mut forms := Array.emptyWithCapacity tokens
  let mut lemmas := Array.emptyWithCapacity tokens
  let mut pos := Array.emptyWithCapacity tokens
  for index in [0:tokens] do
    let dependent := index + 1
    heads := heads.push (if dependent = 1 then 0 else dependent - 1)
    relations := relations.push (if dependent = 1 then "root" else "dep")
    let form := s!"chain{dependent}"
    forms := forms.push form
    lemmas := lemmas.push form
    pos := pos.push (if dependent = 1 then "VERB" else "NOUN")
  let counts : Counts := ⟨tokens, 0, 0⟩
  return {
    name := "long basic chain identity"
    heads := heads
    relations := relations
    forms := forms
    lemmas := lemmas
    pos := pos
    config := { maxCandidates := counts.candidates, maxEdges := counts.total }
    expectedCounts := counts
  }

/-- Construct independent nominal modifiers, each with one direct lexicalizing `case` child. -/
private def nominalFixture (groups : Nat) : Fixture := Id.run do
  let tokens := 1 + 2 * groups
  let mut heads := Array.emptyWithCapacity tokens
  let mut relations := Array.emptyWithCapacity tokens
  let mut forms := Array.emptyWithCapacity tokens
  let mut lemmas := Array.emptyWithCapacity tokens
  let mut pos := Array.emptyWithCapacity tokens
  heads := heads.push 0
  relations := relations.push "root"
  forms := forms.push "buy"
  lemmas := lemmas.push "buy"
  pos := pos.push "VERB"
  for group in [0:groups] do
    let nominal := heads.size + 1
    let nominalForm := s!"item{group}"
    heads := heads.push 1
    relations := relations.push (if group % 2 = 0 then "nmod" else "obl")
    forms := forms.push nominalForm
    lemmas := lemmas.push nominalForm
    pos := pos.push "NOUN"
    heads := heads.push nominal
    relations := relations.push "case"
    let marker := if group % 2 = 0 then "in" else "with"
    forms := forms.push marker
    lemmas := lemmas.push marker
    pos := pos.push "ADP"
  let counts : Counts := ⟨tokens, groups, 0⟩
  return {
    name := s!"nominal case lexicalization ({groups} groups)"
    heads := heads
    relations := relations
    forms := forms
    lemmas := lemmas
    pos := pos
    config := { maxCandidates := counts.candidates, maxEdges := counts.total }
    expectedCounts := counts
  }

/-!
Each coordination level places a non-structural governor below the preceding level's final
conjunct. Every governor then owns a broad set of conjuncts with preceding direct `cc` children.
This makes both lexicalization and incoming-governor propagation fire once per conjunct.
-/

/-- Construct broad coordination groups nested through a non-structural governor at each level. -/
private def conjunctionFixture (levels breadth : Nat) : Fixture := Id.run do
  let tokens := 1 + levels * (1 + 2 * breadth)
  let mut heads := Array.emptyWithCapacity tokens
  let mut relations := Array.emptyWithCapacity tokens
  let mut forms := Array.emptyWithCapacity tokens
  let mut lemmas := Array.emptyWithCapacity tokens
  let mut pos := Array.emptyWithCapacity tokens
  heads := heads.push 0
  relations := relations.push "root"
  forms := forms.push "coordinate"
  lemmas := lemmas.push "coordinate"
  pos := pos.push "VERB"
  let mut anchor := 1
  for level in [0:levels] do
    let governor := heads.size + 1
    heads := heads.push anchor
    relations := relations.push (if level = 0 then "obj" else "dep")
    let governorForm := s!"governor{level}"
    forms := forms.push governorForm
    lemmas := lemmas.push governorForm
    pos := pos.push "NOUN"
    let mut lastConjunct := governor
    for branch in [0:breadth] do
      let conjunction := heads.size + 2
      heads := heads.push conjunction
      relations := relations.push "cc"
      forms := forms.push "and"
      lemmas := lemmas.push "and"
      pos := pos.push "CCONJ"
      heads := heads.push governor
      relations := relations.push "conj"
      let conjunctForm := s!"conjunct{level}_{branch}"
      forms := forms.push conjunctForm
      lemmas := lemmas.push conjunctForm
      pos := pos.push "NOUN"
      lastConjunct := conjunction
    anchor := lastConjunct
  let derived := levels * breadth
  let counts : Counts := ⟨tokens, derived, derived⟩
  return {
    name := "broad nested conjunction propagation"
    heads := heads
    relations := relations
    forms := forms
    lemmas := lemmas
    pos := pos
    config := { maxCandidates := counts.candidates, maxEdges := counts.total }
    expectedCounts := counts
  }

/-- Require two untimed warmups with exact advertised counts and complete output stability. -/
private def warmup (fixture : Fixture) : IO Observation := do
  unless fixture.config.maxCandidates = fixture.expectedCounts.candidates &&
      fixture.config.maxEdges = fixture.expectedCounts.total do
    throw <| IO.userError s!"{fixture.name} does not use exact output budgets"
  let first ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause =>
        throw <| IO.userError s!"{fixture.name} warmup failed: {repr cause}"
  unless first.counts = fixture.expectedCounts &&
      first.nodeCount = fixture.expectedCounts.basic &&
      first.edgeCount = fixture.expectedCounts.total do
    throw <| IO.userError s!"{fixture.name} produced unexpected output accounting"
  let second ←
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .ok value => pure value
    | .error cause =>
        throw <| IO.userError s!"{fixture.name} second warmup failed: {repr cause}"
  unless second = first do
    throw <| IO.userError s!"{fixture.name} output changed between warmups"
  return first

/-- Time one batch while exactly comparing every complete output to the warmup snapshot. -/
private def sample (repetitions : Nat) (fixture : Fixture)
    (expected : Observation) : IO Batch := do
  if repetitions = 0 then
    throw <| IO.userError "enhanced-dependency benchmark requires a positive batch size"
  let start ← IO.monoNanosNow
  let mut aggregate := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    match ← IO.lazyPure fun _ ↦ run fixture with
    | .error cause =>
        throw <| IO.userError s!"{fixture.name} timed run failed: {repr cause}"
    | .ok current =>
        unless current = expected do
          throw <| IO.userError s!"{fixture.name} output changed during timing"
        aggregate := mix aggregate current.checksum
  let stop ← IO.monoNanosNow
  return ⟨stop - start, aggregate⟩

/-- Rescale a checked batch twice toward the requested wall-clock duration. -/
private def calibrateRepetitions (targetNanos : Nat) (fixture : Fixture)
    (expected : Observation) : IO Nat := do
  let mut repetitions := 1
  for _attempt in [0:2] do
    let measured ← sample repetitions fixture expected
    let elapsed := max measured.elapsedNanos 1
    let estimate := (repetitions * targetNanos + elapsed / 2) / elapsed
    repetitions := min 4096 (max estimate 1)
  return repetitions

/-- Sort a small duration sample without adding benchmark dependencies. -/
private def sortNanos (samples : Array Nat) : Array Nat := Id.run do
  let mut sorted := samples
  for leftIndex in [0:sorted.size] do
    for rightIndex in [leftIndex + 1:sorted.size] do
      let left := sorted.getD leftIndex 0
      let right := sorted.getD rightIndex 0
      if right < left then
        sorted := (sorted.set! leftIndex right).set! rightIndex left
  return sorted

/-- Calibrate near 25 ms, then collect a median and range from checked timed batches. -/
private def bench (fixture : Fixture) (expected : Observation) : IO Timing := do
  let batches := 7
  let repetitions ← calibrateRepetitions 25000000 fixture expected
  let mut samples := Array.emptyWithCapacity batches
  let mut aggregate := mix 0 (UInt64.ofNat batches)
  for _batch in [0:batches] do
    let measured ← sample repetitions fixture expected
    samples := samples.push (measured.elapsedNanos / repetitions)
    aggregate := mix aggregate measured.aggregate
  let sorted := sortNanos samples
  return ⟨repetitions, sorted.getD (sorted.size / 2) 0, sorted.getD 0 0,
    sorted.getD (sorted.size - 1) 0, aggregate⟩

/-- Report per-run latency, calibrated batch duration, and token and edge throughput. -/
private def report (fixture : Fixture) (timing : Timing) : IO Unit := do
  let seconds := Float.ofNat (max timing.medianNanos 1) / 1000000000.0
  let tokensPerSecond := Float.ofNat fixture.heads.size / seconds
  let edgesPerSecond := Float.ofNat fixture.expectedCounts.total / seconds
  IO.println <| s!"{fixture.name} [checked end-to-end]: tokens={fixture.heads.size} " ++
    s!"edges={fixture.expectedCounts.total} " ++
    s!"derived={fixture.expectedCounts.candidates} repetitions={timing.repetitions} " ++
    s!"batch~={timing.medianNanos * timing.repetitions / 1000000} ms " ++
    s!"median={timing.medianNanos / 1000} us " ++
    s!"range=[{timing.minNanos / 1000}, {timing.maxNanos / 1000}] us " ++
    s!"tokens/s={tokensPerSecond} edges/s={edgesPerSecond} chk={timing.aggregate}"

/-- Validate, warm, time, and report one fully materialized fixture. -/
private def runFixture (fixture : Fixture) : IO Unit := do
  let expected ← warmup fixture
  let timing ← bench fixture expected
  report fixture timing

/-- Build all fixtures before entering any timed benchmark region. -/
private def fixtures : Array Fixture :=
  #[identityFixture 16384, nominalFixture 2048, nominalFixture 8192,
    conjunctionFixture 128 64]

/-- Run identity, two nominal fan-out scales, and nested coordination-propagation lanes. -/
def main : IO Unit := do
  let compiledFixtures := fixtures
  for fixture in compiledFixtures do
    runFixture fixture

end EnhancedDependencyBenchmark

def main : IO Unit := EnhancedDependencyBenchmark.main
