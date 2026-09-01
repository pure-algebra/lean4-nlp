import Nlp.Sequence.NerTagger

/-!
# Named entity tagging range benchmark

This standalone benchmark compares complete per-sentence `tagForms` calls, rich encode-once
`tagEncodedRange` calls, and flat encode-once `classesEncodedRange` calls at identical sentence
boundaries. Rich observations consume dense states, typed BIO2 tags, canonical labels, flat
classes, validated mentions, and exact decoder cost bits. The flat lane consumes every class and
must equal the rich class stream. Timings have no machine-specific threshold.
-/

namespace NerBenchmark

open Nlp Nlp.Sequence

/-- One named benchmark lane with a fixed total shape and repetition count. -/
private structure Lane where
  /-- Human-readable size class. -/
  name : String
  /-- Number of tokens decoded under each sentence-level dynamic program. -/
  sentenceLength : Nat
  /-- Number of independently decoded sentences. -/
  sentenceCount : Nat
  /-- Timed repetitions after an untimed warm-up. -/
  repetitions : Nat

/-- Prebuilt input columns and their exact sentence boundaries. -/
private structure Fixture where
  /-- Original per-sentence form columns used by the complete-form path. -/
  sentences : Array (Array String)
  /-- Concatenated document form column used by the encode-once path. -/
  forms : Array String
  /-- Ordered half-open sentence ranges over `forms`. -/
  ranges : Array (Nat × Nat)
  /-- Number of forms found in the exact model vocabulary. -/
  knownCount : Nat
  /-- Number of forms routed through the collision-free OOV identifier. -/
  oovCount : Nat

/-- Fully consumed observable output of one benchmark path. -/
private structure Observation where
  /-- Fixed-width checksum over every result projection. -/
  checksum : UInt64
  /-- Independent checksum over exact floating-point decoder cost bits. -/
  costChecksum : UInt64
  /-- Independent checksum over sentence boundaries and every flat class. -/
  classChecksum : UInt64
  /-- Number of dense numeric states consumed. -/
  stateCount : Nat
  /-- Number of typed BIO2 tags consumed. -/
  typedCount : Nat
  /-- Number of canonical BIO2 labels consumed. -/
  labelCount : Nat
  /-- Number of flat CoreNLP-style entity classes consumed. -/
  classCount : Nat
  /-- Number of validated entity mentions consumed. -/
  mentionCount : Nat
deriving Inhabited, Repr, DecidableEq

/-- Mutable-style accumulator used to assemble one observation without intermediate arrays. -/
private structure Accumulator where
  checksum : UInt64 := 0
  costChecksum : UInt64 := 0
  classChecksum : UInt64 := 0
  stateCount : Nat := 0
  typedCount : Nat := 0
  labelCount : Nat := 0
  classCount : Nat := 0
  mentionCount : Nat := 0

/-- Fully consumed output of the allocation-reduced flat-class path. -/
private structure ClassObservation where
  /-- Checksum over identical sentence boundaries and every emitted class. -/
  checksum : UInt64
  /-- Number of flat classes consumed. -/
  classCount : Nat
deriving Inhabited, Repr, DecidableEq

/-- Average wall time and an aggregate checksum keeping every repetition observable. -/
private structure Timing where
  nanos : Nat
  checksum : UInt64

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Mix a complete string, including its byte width, without relying on runtime hash seeding. -/
private def mixString (state : UInt64) (value : String) : UInt64 := Id.run do
  let mut checksum := mix state (UInt64.ofNat value.utf8ByteSize)
  for character in value.toList do
    checksum := mix checksum (UInt64.ofNat character.toNat)
  return checksum

/-- Mix exact global boundaries and every flat class in source order. -/
private def mixClasses (state : UInt64) (start stop : Nat)
    (classes : Array String) : UInt64 := Id.run do
  let mut checksum := mix state (UInt64.ofNat start)
  checksum := mix checksum (UInt64.ofNat stop)
  checksum := mix checksum (UInt64.ofNat classes.size)
  for entityClass in classes do
    checksum := mixString checksum entityClass
  return checksum

/-- Mix the constructor and exact entity name of one typed BIO2 tag. -/
@[inline] private def mixTag (state : UInt64) : Bio.Tag → UInt64
  | .outside => mix state 0
  | .begin entity => mixString (mix state 1) entity.name
  | .inside entity => mixString (mix state 2) entity.name

/-- Ordered canonical BIO2 state labels used by the deterministic fixture model. -/
private def tagLabels : Array String :=
  #["O", "B-PERSON", "I-PERSON", "B-ORGANIZATION", "I-ORGANIZATION",
    "B-LOCATION", "I-LOCATION", "B-DATE", "I-DATE"]

/-- Number of twelve-token vocabulary templates retained by the model. -/
private def vocabularyBuckets : Nat := 16

/-- Exact case-sensitive vocabulary used by both model and benchmark fixtures. -/
private def wordNames : Array String :=
  Array.ofFn (n := vocabularyBuckets * 12) fun index ↦ s!"known{index.val}"

/-- Desired dense BIO2 state for one position in a twelve-token fixture template. -/
@[inline] private def targetState : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 3 => 3
  | 4 => 4
  | 6 => 5
  | 7 => 6
  | 9 => 7
  | 10 => 8
  | _ => 0

/-- Wrap one finite nonnegative synthetic score as an operational min-plus cost. -/
@[inline] private def cost (value : Float) : Cost :=
  ⟨value⟩

/-- Dense emissions with a unique, BIO2-legal preferred tag for every known form. -/
private def emissions : Std.HashMap UInt64 Cost := Id.run do
  let mut result : Std.HashMap UInt64 Cost := {}
  for state in [0:tagLabels.size] do
    for word in [0:wordNames.size] do
      let expected := targetState (word % 12)
      let value := if state == expected then 0.0 else 16.0
      result := result.insert (Hmm.emissionKey state (UInt32.ofNat word)) (cost value)
  return result

/-- Numeric model whose unknown-word distribution deterministically prefers `O`. -/
private def numericModel : Hmm where
  nTags := tagLabels.size
  start := Array.replicate tagLabels.size (cost 0.0)
  trans := Array.replicate (tagLabels.size * tagLabels.size) (cost 0.0)
  emit := emissions
  unk := Array.ofFn (n := tagLabels.size) fun state ↦
    cost (if state.val == 0 then 0.0 else 16.0)

/-- Compile the named benchmark model once, outside every timed region. -/
private def tagger? : Except NerTagger.CompileError NerTagger :=
  NerTagger.compile numericModel wordNames tagLabels

/-- Select a known form with the requested twelve-token template role. -/
@[inline] private def knownForm (sentence position : Nat) : String :=
  let role := position % 12
  let bucket := (sentence * 7 + position / 12 * 11 + role * 3) % vocabularyBuckets
  wordNames[bucket * 12 + role]!

/-- Build one fixture before timing, with known and OOV forms in every sentence. -/
private def buildFixture (lane : Lane) : Fixture := Id.run do
  let total := lane.sentenceCount * lane.sentenceLength
  let mut sentences := Array.emptyWithCapacity lane.sentenceCount
  let mut forms := Array.emptyWithCapacity total
  let mut ranges := Array.emptyWithCapacity lane.sentenceCount
  let mut knownCount := 0
  let mut oovCount := 0
  for sentenceIndex in [0:lane.sentenceCount] do
    let start := forms.size
    let mut sentence := Array.emptyWithCapacity lane.sentenceLength
    for position in [0:lane.sentenceLength] do
      let role := position % 12
      let form :=
        if role == 2 || role == 8 then
          s!"unseen-{sentenceIndex}-{position}"
        else
          knownForm sentenceIndex position
      if role == 2 || role == 8 then
        oovCount := oovCount + 1
      else
        knownCount := knownCount + 1
      sentence := sentence.push form
      forms := forms.push form
    sentences := sentences.push sentence
    ranges := ranges.push (start, forms.size)
  return ⟨sentences, forms, ranges, knownCount, oovCount⟩

/-- Consume one tagging and its independently exposed constrained-decoder result. -/
private def absorb (prior : Accumulator) (coordinateOffset : Nat)
    (tagging : NerTagger.Tagging) (decoded : ConstrainedHmm.DecodeResult) : Accumulator :=
  Id.run do
    let globalStart := coordinateOffset + tagging.start
    let globalStop := coordinateOffset + tagging.stop
    let mut checksum := mix prior.checksum (UInt64.ofNat globalStart)
    checksum := mix checksum (UInt64.ofNat globalStop)
    checksum := mix checksum (UInt64.ofNat decoded.tags.size)
    for state in decoded.tags do
      checksum := mix checksum (UInt64.ofNat state)
    checksum := mix checksum (UInt64.ofNat tagging.tags.size)
    for tag in tagging.tags do
      checksum := mixTag checksum tag
    checksum := mix checksum (UInt64.ofNat tagging.labels.size)
    for label in tagging.labels do
      checksum := mixString checksum label
    checksum := mix checksum (UInt64.ofNat tagging.classes.size)
    for entityClass in tagging.classes do
      checksum := mixString checksum entityClass
    checksum := mix checksum (UInt64.ofNat tagging.mentions.size)
    for mention in tagging.mentions do
      checksum := mix checksum (UInt64.ofNat (coordinateOffset + mention.start))
      checksum := mix checksum (UInt64.ofNat (coordinateOffset + mention.stop))
      checksum := mixString checksum mention.entity.name
    checksum := mix checksum decoded.cost.toFloat.toBits
    return {
      checksum
      costChecksum := mix prior.costChecksum decoded.cost.toFloat.toBits
      classChecksum := mixClasses prior.classChecksum globalStart globalStop tagging.classes
      stateCount := prior.stateCount + decoded.tags.size
      typedCount := prior.typedCount + tagging.tags.size
      labelCount := prior.labelCount + tagging.labels.size
      classCount := prior.classCount + tagging.classes.size
      mentionCount := prior.mentionCount + tagging.mentions.size
    }

/-- Freeze an accumulator into the equality-comparable observation exposed by timed paths. -/
@[inline] private def finish (result : Accumulator) : Observation :=
  { checksum := result.checksum
    costChecksum := result.costChecksum
    classChecksum := result.classChecksum
    stateCount := result.stateCount
    typedCount := result.typedCount
    labelCount := result.labelCount
    classCount := result.classCount
    mentionCount := result.mentionCount }

/-- Seed both independently checked streams from a runtime-varying observation salt. -/
@[inline] private def initialAccumulator (salt : UInt64) : Accumulator :=
  { checksum := mix 0 salt
    costChecksum := mix 1 salt
    classChecksum := mix 2 salt }

/-- Tag each sentence through the complete-form API and consume every exposed projection. -/
@[noinline] private def observeWholeForms (salt : UInt64) (tagger : NerTagger)
    (fixture : Fixture) :
    Except NerTagger.TagError Observation := do
  let mut result := initialAccumulator salt
  let mut offset := 0
  for sentence in fixture.sentences do
    let tagging ← tagger.tagForms sentence
    let decoded := tagger.model.decodeResult (tagger.encodeForms sentence)
    result := absorb result offset tagging decoded
    offset := offset + sentence.size
  return finish result

/-- Encode one document column and tag all sentence ranges without allocating string slices. -/
@[noinline] private def observeEncodedRanges (salt : UInt64) (tagger : NerTagger)
    (fixture : Fixture) :
    Except NerTagger.TagError Observation := do
  let encoded := tagger.encodeForms fixture.forms
  let mut result := initialAccumulator salt
  for range in fixture.ranges do
    let tagging ← tagger.tagEncodedRange encoded range.1 range.2
    let decoded := tagger.model.decodeRangeResult encoded range.1 range.2
    result := absorb result 0 tagging decoded
  return finish result

/-- Encode one document and consume only flat classes for every sentence range. -/
@[noinline] private def observeEncodedClasses (salt : UInt64) (tagger : NerTagger)
    (fixture : Fixture) : Except NerTagger.TagError ClassObservation := do
  let encoded := tagger.encodeForms fixture.forms
  let mut checksum := mix 2 salt
  let mut classCount := 0
  for range in fixture.ranges do
    let classes ← tagger.classesEncodedRange encoded range.1 range.2
    checksum := mixClasses checksum range.1 range.2 classes
    classCount := classCount + classes.size
  return ⟨checksum, classCount⟩

/-- Project the class-only parity contract from one rich observation. -/
@[inline] private def classesOfRich (observation : Observation) : ClassObservation :=
  ⟨observation.classChecksum, observation.classCount⟩

/-- Require one successful observation while retaining typed tagging diagnostics. -/
private def requireObservation (name : String)
    (result : Except NerTagger.TagError Observation) : IO Observation :=
  match result with
  | .ok observation => pure observation
  | .error cause => throw <| IO.userError s!"{name} failed: {repr cause}"

/-- Require one successful flat-class observation with typed failure diagnostics. -/
private def requireClassObservation (name : String)
    (result : Except NerTagger.TagError ClassObservation) : IO ClassObservation :=
  match result with
  | .ok observation => pure observation
  | .error cause => throw <| IO.userError s!"{name} failed: {repr cause}"

/-- Warm up, time repeated observations, and reject checksum instability. -/
private def benchPath (name : String) (repetitions : Nat)
    (run : UInt64 → Except NerTagger.TagError Observation) : IO Timing := do
  let mut expected := Array.emptyWithCapacity repetitions
  for index in [0:repetitions] do
    let salt := UInt64.ofNat (index + 1)
    let observation ← requireObservation name (← IO.lazyPure fun _ ↦ run salt)
    expected := expected.push observation
  let start ← IO.monoNanosNow
  let mut aggregate := mix 0 (UInt64.ofNat repetitions)
  for index in [0:repetitions] do
    let salt := UInt64.ofNat (index + 1)
    let current ← requireObservation name (← IO.lazyPure fun _ ↦ run salt)
    if current != expected[index]! then
      throw <| IO.userError s!"{name} observation changed"
    aggregate := mix aggregate current.checksum
    aggregate := mix aggregate current.costChecksum
    aggregate := mix aggregate current.classChecksum
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Time flat-class projection against per-salt rich observations computed before timing. -/
private def benchClassPath (name : String) (repetitions : Nat)
    (rich : UInt64 → Except NerTagger.TagError Observation)
    (run : UInt64 → Except NerTagger.TagError ClassObservation) : IO Timing := do
  let mut expected := Array.emptyWithCapacity repetitions
  for index in [0:repetitions] do
    let salt := UInt64.ofNat (index + 1)
    let observation ← requireObservation s!"{name} rich reference" <|
      ← IO.lazyPure fun _ ↦ rich salt
    expected := expected.push (classesOfRich observation)
  let start ← IO.monoNanosNow
  let mut aggregate := mix 0 (UInt64.ofNat repetitions)
  for index in [0:repetitions] do
    let salt := UInt64.ofNat (index + 1)
    let current ← requireClassObservation name (← IO.lazyPure fun _ ↦ run salt)
    if current != expected[index]! then
      throw <| IO.userError s!"{name} differs from rich tagging"
    aggregate := mix aggregate current.checksum
    aggregate := mix aggregate (UInt64.ofNat current.classCount)
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Verify that all token-aligned outputs were forced for one fixture. -/
private def completeObservation (tokens : Nat) (observation : Observation) : Bool :=
  observation.stateCount == tokens && observation.typedCount == tokens &&
    observation.labelCount == tokens && observation.classCount == tokens

/-- Report one path in wall time and token throughput without asserting a machine threshold. -/
private def report (name : String) (tokens : Nat) (timing : Timing) : IO Unit := do
  let seconds := Float.ofNat (max timing.nanos 1) / 1000000000.0
  let throughput := Float.ofNat tokens / seconds
  IO.println <| s!"{name}: elapsed={timing.nanos / 1000} us " ++
    s!"tokens/s={throughput} chk={timing.checksum}"

/-- Validate parity, then time all three tagging paths for one sentence-length class. -/
private def benchLane (tagger : NerTagger) (lane : Lane) : IO Unit := do
  let fixture := buildFixture lane
  let expectedTokens := lane.sentenceLength * lane.sentenceCount
  unless fixture.forms.size == expectedTokens &&
      fixture.sentences.size == lane.sentenceCount &&
      fixture.ranges.size == lane.sentenceCount &&
      0 < fixture.knownCount && 0 < fixture.oovCount do
    throw <| IO.userError s!"{lane.name} NER fixture shape changed"
  let whole ← requireObservation "whole-form NER warm-up" <|
    observeWholeForms 0 tagger fixture
  let ranged ← requireObservation "encode-once NER warm-up" <|
    observeEncodedRanges 0 tagger fixture
  let classes ← requireClassObservation "flat-class NER warm-up" <|
    observeEncodedClasses 0 tagger fixture
  unless whole == ranged do
    throw <| IO.userError s!"{lane.name} whole-form/range observations differ"
  unless classes == classesOfRich ranged do
    throw <| IO.userError s!"{lane.name} flat classes differ from rich tagging"
  unless completeObservation expectedTokens whole do
    throw <| IO.userError s!"{lane.name} did not consume every token-aligned output"
  IO.println <| s!"--- {lane.name}: sentences={lane.sentenceCount} " ++
    s!"sentenceLength={lane.sentenceLength} tokens={expectedTokens} " ++
    s!"known={fixture.knownCount} oov={fixture.oovCount} " ++
    s!"mentions={whole.mentionCount} repetitions={lane.repetitions} ---"
  let wholeTiming ← benchPath "whole-form NER" lane.repetitions fun salt ↦
    observeWholeForms salt tagger fixture
  report "complete tagForms per sentence" expectedTokens wholeTiming
  let rangeTiming ← benchPath "encode-once NER" lane.repetitions fun salt ↦
    observeEncodedRanges salt tagger fixture
  report "encode once + sentence ranges" expectedTokens rangeTiming
  let classTiming ←
    benchClassPath "flat-class NER" lane.repetitions
      (fun salt ↦ observeEncodedRanges salt tagger fixture)
      (fun salt ↦ observeEncodedClasses salt tagger fixture)
  report "encode once + flat class ranges" expectedTokens classTiming
  IO.println s!"rich range/whole speedup={
    Float.ofNat wholeTiming.nanos / Float.ofNat (max rangeTiming.nanos 1)}x"
  IO.println s!"flat classes/rich range speedup={
    Float.ofNat rangeTiming.nanos / Float.ofNat (max classTiming.nanos 1)}x"

/-- Run short-, medium-, and long-sentence deterministic NER benchmark lanes. -/
def main : IO Unit := do
  let tagger ←
    match tagger? with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"NER benchmark model failed: {repr cause}"
  IO.println <| s!"vocabulary={tagger.wordNames.size}; states={tagger.nStates}; " ++
    s!"labels={tagger.tagLabels.size}"
  let lanes : Array Lane :=
    #[⟨"short", 12, 512, 6⟩, ⟨"medium", 48, 128, 5⟩, ⟨"long", 192, 32, 3⟩]
  for lane in lanes do
    benchLane tagger lane

end NerBenchmark

def main : IO Unit := NerBenchmark.main
