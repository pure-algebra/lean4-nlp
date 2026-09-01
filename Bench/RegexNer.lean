import Nlp.Pattern.Automaton
import Nlp.Pattern.Phrase

/-!
# RegexNER and token-pattern benchmark

This native benchmark compares exact token-phrase Aho--Corasick search with an independently
shaped brute-force scan. A second, smaller lane compares compiled Thompson-NFA overlap search with
the executable `Regular.endpoints` reference semantics. Fixtures and automata are built before
timing, every result field contributes to a deterministic checksum, and exact finite match sets
must agree before either implementation is measured. No machine-specific threshold is asserted.
-/

namespace RegexNerBenchmark

open Nlp.Pattern

/-- Stable public representation of one rule and its half-open token span. -/
private abbrev Signature := Nat × Nat × Nat

/-- Number of produced matches and a checksum over every public result field. -/
private structure Observation where
  count : Nat
  checksum : UInt64
  deriving Repr, DecidableEq

/-- Average elapsed wall time and an aggregate checksum across all repetitions. -/
private structure Timing where
  nanos : Nat
  checksum : UInt64

/-- One phrase-search workload size and repetition policy. -/
private structure PhraseLane where
  name : String
  tokens : Nat
  repetitions : Nat

/-- One regular-pattern workload size and repetition policy. -/
private structure NfaLane where
  name : String
  tokens : Nat
  repetitions : Nat

/-- Compiled exact phrases and their full-column range fixture. -/
private structure PhraseFixture where
  phrases : Array (Array String)
  automaton : PhraseAutomaton
  forms : Array String
  start : Nat
  stop : Nat

/-- Compiled regular rules and their full-column symbolic input fixture. -/
private structure NfaFixture where
  patterns : Array (Regular Nat)
  automaton : Automaton Nat
  input : Array Nat
  start : Nat
  stop : Nat

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Fold one public match signature into a checksum. -/
@[inline] private def mixSignature (state : UInt64) (signature : Signature) : UInt64 :=
  let state := mix state (UInt64.ofNat signature.1)
  let state := mix state (UInt64.ofNat signature.2.1)
  mix state (UInt64.ofNat signature.2.2)

/-- Build a hash set for exact order-independent parity checks. -/
private def signatureSet (values : Array Signature) : Std.HashSet Signature := Id.run do
  let mut result : Std.HashSet Signature := {}
  for value in values do
    result := result.insert value
  return result

/-- Compare unique rule/span candidates as exact finite sets. -/
private def sameCandidateSet (left right : Array Signature) : Bool :=
  let leftSet := signatureSet left
  let rightSet := signatureSet right
  left.size == right.size && leftSet.size == left.size && rightSet.size == right.size &&
    left.all rightSet.contains && right.all leftSet.contains

/-- Project proof-carrying phrase matches to stable source ordinals and spans. -/
private def phraseSignatures (found : Array PhraseMatch) : Array Signature :=
  found.map fun matched ↦ (matched.rule, matched.start, matched.stop)

/-- Project proof-carrying NFA matches to stable source ordinals and spans. -/
private def nfaSignatures (found : Array Match) : Array Signature :=
  found.map fun matched ↦ (matched.rule, matched.start, matched.stop)

/-- Stable exact-token spelling for phrase vocabulary ordinal `word`. -/
@[inline] private def wordName (word : Nat) : String :=
  s!"token-{word}"

/-- Number of exact spellings in the phrase benchmark vocabulary. -/
private def phraseVocabulary : Nat := 32

/--
Build shared-prefix and shared-suffix exact rules in nonincreasing length order.

Every rule is a cyclic substring of the same finite vocabulary, so ordinary input positions
produce matches of several widths while periodic unknown forms exercise root resets.
-/
private def phraseSource : Array (Array String) := Id.run do
  let mut output := #[]
  for lengthOffset in [0:4] do
    let length := 4 - lengthOffset
    for first in [0:phraseVocabulary] do
      let phrase := Array.ofFn (n := length) fun offset ↦
        wordName ((first + offset.val) % phraseVocabulary)
      output := output.push phrase
  return output

/-- Build a padded form column with deterministic, collision-free unknown tokens. -/
private def phraseForms (tokens padding : Nat) : Array String :=
  Array.ofFn (n := tokens + padding * 2) fun index ↦
    if index.val < padding || padding + tokens ≤ index.val then
      s!"outside-{index.val}"
    else
      let position := index.val - padding
      if position % 97 = 96 then s!"unknown-{position}"
      else wordName (position % phraseVocabulary)

/-- Compile one exact-phrase fixture outside every timed region. -/
private def buildPhraseFixture (tokens : Nat) : Except PhraseCompileError PhraseFixture := do
  let phrases := phraseSource
  let automaton ← PhraseAutomaton.compile phrases
  let padding := 3
  return ⟨phrases, automaton, phraseForms tokens padding, padding, padding + tokens⟩

/-- Check one source phrase at an absolute full-column position without slicing the input. -/
private def phraseAt (phrase forms : Array String) (position upper : Nat) : Bool := Id.run do
  if upper < position + phrase.size then
    return false
  for offset in [0:phrase.size] do
    if phrase[offset]! != forms[position + offset]! then
      return false
  return true

/-- Brute-force exact phrases in source-rule then absolute-start order. -/
private def phraseReference (phrases : Array (Array String)) (forms : Array String)
    (start stop : Nat) : Array Signature := Id.run do
  let (lower, upper) := PhraseAutomaton.normalizeRange forms.size start stop
  let mut output := #[]
  for rule in [0:phrases.size] do
    let phrase := phrases[rule]!
    for position in [lower:upper] do
      let after := position + phrase.size
      if after ≤ upper && phraseAt phrase forms position upper then
        output := output.push (rule, position, after)
  return output

/-- Evaluate one natural-number atom at an absolute input position. -/
@[inline] private def holdsAt (input : Array Nat) (atom position : Nat) : Bool :=
  input[position]? == some atom

/-- Nonnullable regular rules with exact, alternative, sequence, and star structure. -/
private def nfaPatterns : Array (Regular Nat) :=
  #[.seq (.atom 0) (.atom 1),
    .seq (.atom 0) (.seq (.star (.atom 1)) (.atom 2)),
    .alt (.seq (.atom 2) (.atom 3)) (.atom 4),
    .seq (.atom 3) (.seq (.star (.atom 3)) (.atom 4)),
    .seq (.star (.alt (.atom 0) (.atom 4))) (.atom 2),
    .seq (.atom 4) (.alt (.atom 0) (.seq (.atom 1) (.atom 2)))]

/-- Repeating token block chosen to exercise every source regular rule. -/
private def nfaBlock : Array Nat := #[0, 1, 1, 2, 3, 3, 4, 2, 4, 0, 4, 1, 2]

/-- Build a padded symbolic input with values absent from every source rule. -/
private def nfaInput (tokens padding : Nat) : Array Nat :=
  Array.ofFn (n := tokens + padding * 2) fun index ↦
    if index.val < padding || padding + tokens ≤ index.val then
      99
    else
      nfaBlock.getD ((index.val - padding) % nfaBlock.size) 99

/-- Compile one regular-pattern fixture outside every timed region. -/
private def buildNfaFixture (tokens : Nat) : Except CompileError NfaFixture := do
  let patterns := nfaPatterns
  let automaton ← Automaton.compile patterns
  let padding := 2
  return ⟨patterns, automaton, nfaInput tokens padding, padding, padding + tokens⟩

/-- Enumerate reference matches with the finite executable regular semantics. -/
private def nfaReference (patterns : Array (Regular Nat)) (input : Array Nat)
    (start stop : Nat) : Array Signature := Id.run do
  let range := Nlp.Pattern.normalizeRange input.size start stop
  let holds := holdsAt input
  let mut output := #[]
  for candidateStart in [range.start:range.stop] do
    for rule in [0:patterns.size] do
      if let some pattern := patterns[rule]? then
        for candidateStop in pattern.endpoints holds candidateStart range.stop do
          if candidateStart < candidateStop then
            output := output.push (rule, candidateStart, candidateStop)
  return output

/-- Consume every field of an Aho--Corasick result without allocating a projected result array. -/
@[noinline] private def observePhraseAutomaton (fixture : PhraseFixture) : Observation := Id.run do
  let limit := fixture.phrases.size * (fixture.stop - fixture.start)
  let .ok found :=
      fixture.automaton.findAllRangeWithLimit limit fixture.forms fixture.start fixture.stop
    | return ⟨0, 0⟩
  let mut checksum := mix 0 (UInt64.ofNat found.size)
  for matched in found do
    checksum := mixSignature checksum (matched.rule, matched.start, matched.stop)
  return ⟨found.size, checksum⟩

/-- Consume every field of a brute-force exact-phrase result. -/
@[noinline] private def observePhraseReference (fixture : PhraseFixture) : Observation := Id.run do
  let found := phraseReference fixture.phrases fixture.forms fixture.start fixture.stop
  let mut checksum := mix 0 (UInt64.ofNat found.size)
  for signature in found do
    checksum := mixSignature checksum signature
  return ⟨found.size, checksum⟩

/-- Consume every field of a compiled overlapping NFA result. -/
@[noinline] private def observeNfaAutomaton (fixture : NfaFixture) : Observation := Id.run do
  let holds := holdsAt fixture.input
  let config : SearchConfig := {
    maxWork := fixture.automaton.overlapWorkUpperBound fixture.input.size
      fixture.start fixture.stop
    maxMatches := fixture.patterns.size * (fixture.stop - fixture.start + 1) ^ 2
  }
  let .ok found := fixture.automaton.findOverlappingRangeWith config holds fixture.input.size
      fixture.start fixture.stop
    | return ⟨0, 0⟩
  let mut checksum := mix 0 (UInt64.ofNat found.size)
  for matched in found do
    checksum := mixSignature checksum (matched.rule, matched.start, matched.stop)
  return ⟨found.size, checksum⟩

/-- Consume every field of the executable regular-semantics result. -/
@[noinline] private def observeNfaReference (fixture : NfaFixture) : Observation := Id.run do
  let found := nfaReference fixture.patterns fixture.input fixture.start fixture.stop
  let mut checksum := mix 0 (UInt64.ofNat found.size)
  for signature in found do
    checksum := mixSignature checksum signature
  return ⟨found.size, checksum⟩

/-- Warm up and time one completely observed deterministic path. -/
private def benchPath (name : String) (repetitions : Nat)
    (run : Unit → Observation) : IO Timing := do
  let expected ← IO.lazyPure fun _ ↦ run ()
  let start ← IO.monoNanosNow
  let mut aggregate := mix expected.checksum (UInt64.ofNat expected.count)
  for _ in [0:repetitions] do
    let current ← IO.lazyPure fun _ ↦ run ()
    if current != expected then
      throw <| IO.userError s!"{name} observation changed"
    aggregate := mix aggregate current.checksum
    aggregate := mix aggregate (UInt64.ofNat current.count)
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / max repetitions 1, aggregate⟩

/-- Report elapsed time, token throughput, match count, and forced checksum. -/
private def report (name : String) (tokens matchCount : Nat) (timing : Timing) : IO Unit := do
  let seconds := Float.ofNat (max timing.nanos 1) / 1000000000.0
  let throughput := Float.ofNat tokens / seconds
  IO.println <| s!"{name}: elapsed={timing.nanos / 1000} us " ++
    s!"tokens/s={throughput} matches={matchCount} chk={timing.checksum}"

/-- Check exact candidate parity, then time one exact-phrase workload. -/
private def benchPhraseLane (lane : PhraseLane) : IO Unit := do
  let fixture ←
    match buildPhraseFixture lane.tokens with
    | .ok value => pure value
    | .error cause =>
        throw <| IO.userError s!"{lane.name} phrase compilation failed: {repr cause}"
  let limit := fixture.phrases.size * (fixture.stop - fixture.start)
  let actual ←
    match fixture.automaton.findAllRangeWithLimit limit fixture.forms
        fixture.start fixture.stop with
    | .ok found => pure (phraseSignatures found)
    | .error cause =>
        throw <| IO.userError s!"{lane.name} bounded phrase search failed: {repr cause}"
  let expected := phraseReference fixture.phrases fixture.forms fixture.start fixture.stop
  unless sameCandidateSet actual expected do
    throw <| IO.userError s!"{lane.name} Aho--Corasick/reference candidates differ"
  unless 0 < actual.size do
    throw <| IO.userError s!"{lane.name} exact-phrase fixture produced no matches"
  IO.println <| s!"--- phrase {lane.name}: tokens={lane.tokens} " ++
    s!"rules={fixture.automaton.ruleCount} nodes={fixture.automaton.nodeCount} " ++
    s!"vocabulary={fixture.automaton.vocabularySize} matches={actual.size} " ++
    s!"repetitions={lane.repetitions} ---"
  let aho ← benchPath "Aho--Corasick phrase search" lane.repetitions fun _ ↦
    observePhraseAutomaton fixture
  report "Aho--Corasick phrase search" lane.tokens actual.size aho
  let brute ← benchPath "brute exact-phrase scan" lane.repetitions fun _ ↦
    observePhraseReference fixture
  report "brute exact-phrase scan" lane.tokens expected.size brute
  IO.println s!"phrase brute/Aho ratio={
    Float.ofNat brute.nanos / Float.ofNat (max aho.nanos 1)}x"

/-- Check exact candidate parity, then time one general regular-pattern workload. -/
private def benchNfaLane (lane : NfaLane) : IO Unit := do
  let fixture ←
    match buildNfaFixture lane.tokens with
    | .ok value => pure value
    | .error cause =>
        throw <| IO.userError s!"{lane.name} NFA compilation failed: {repr cause}"
  let holds := holdsAt fixture.input
  let search : SearchConfig := {
    maxWork := fixture.automaton.overlapWorkUpperBound fixture.input.size
      fixture.start fixture.stop
    maxMatches := fixture.patterns.size * (fixture.stop - fixture.start + 1) ^ 2
  }
  let actual ←
    match fixture.automaton.findOverlappingRangeWith search holds fixture.input.size
        fixture.start fixture.stop with
    | .ok found => pure (nfaSignatures found)
    | .error cause =>
        throw <| IO.userError s!"{lane.name} bounded NFA search failed: {repr cause}"
  let expected := nfaReference fixture.patterns fixture.input fixture.start fixture.stop
  unless sameCandidateSet actual expected do
    throw <| IO.userError s!"{lane.name} compiled/reference NFA candidates differ"
  unless 0 < actual.size do
    throw <| IO.userError s!"{lane.name} regular-pattern fixture produced no matches"
  IO.println <| s!"--- NFA {lane.name}: tokens={lane.tokens} " ++
    s!"rules={fixture.automaton.ruleCount} states={fixture.automaton.stateCount} " ++
    s!"edges={fixture.automaton.edgeCount} matches={actual.size} " ++
    s!"repetitions={lane.repetitions} ---"
  let compiled ← benchPath "compiled Thompson NFA" lane.repetitions fun _ ↦
    observeNfaAutomaton fixture
  report "compiled Thompson NFA" lane.tokens actual.size compiled
  let reference ← benchPath "regular reference semantics" lane.repetitions fun _ ↦
    observeNfaReference fixture
  report "regular reference semantics" lane.tokens expected.size reference
  IO.println s!"reference/compiled NFA ratio={
    Float.ofNat reference.nanos / Float.ofNat (max compiled.nanos 1)}x"

/-- Run deterministic exact-phrase and general regular-pattern benchmark lanes. -/
def main : IO Unit := do
  let phraseLanes : Array PhraseLane :=
    #[⟨"small", 2_048, 5⟩, ⟨"medium", 8_192, 3⟩, ⟨"large", 32_768, 1⟩]
  for lane in phraseLanes do
    benchPhraseLane lane
  let nfaLanes : Array NfaLane :=
    #[⟨"small", 32, 5⟩, ⟨"medium", 64, 3⟩, ⟨"large", 128, 1⟩]
  for lane in nfaLanes do
    benchNfaLane lane

end RegexNerBenchmark

def main : IO Unit := RegexNerBenchmark.main
