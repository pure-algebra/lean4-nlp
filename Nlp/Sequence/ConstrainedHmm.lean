import Nlp.Sequence.Bio
import Nlp.Sequence.Hmm

/-!
# Compiled BIO-constrained hidden Markov decoding

`ConstrainedHmm` validates an existing numeric HMM against an ordered BIO2 inventory, then
compiles legal predecessors into a compact row index. Decoding visits predecessors in ascending
state order, so strict improvements retain the first path on exact ties. A separate reachability
array prevents an overflowed `+infinity` score from being confused with an impossible state.
-/

namespace Nlp.Sequence

/-- Why an HMM and ordered BIO2 inventory could not form a constrained decoder. -/
inductive ConstrainedHmmCompileError where
  | stateCapacity (count : Nat)
  | invalidDimensions (nTags start transitions unknown : Nat)
  | invalidTagCount (expected found : Nat)
  | duplicateTag (first duplicate : Nat) (label : String)
  | missingOutside
  | orphanInside (index : Nat) (entity : String)
  | invalidStartCost (index : Nat) (value : Float) (bits : UInt64)
  | invalidTransitionCost (index : Nat) (value : Float) (bits : UInt64)
  | invalidUnknownCost (index : Nat) (value : Float) (bits : UInt64)
  | invalidEmissionCost (key : UInt64) (value : Float) (bits : UInt64)
  | emissionTagOutOfRange (key : UInt64) (tag nTags : Nat)
deriving Repr

/-- A validated HMM with a compiled BIO2 start set and predecessor index. -/
structure ConstrainedHmm where
  private mk ::
  /-- The validated numeric scoring model. -/
  hmm : Hmm
  /-- Ordered BIO2 states corresponding exactly to `hmm` states. -/
  tags : Array Bio.Tag
  /-- Dense ordinal of the unique outside state. -/
  outside : UInt32
  /-- Legal first-position states in ascending ordinal order. -/
  startStates : Array UInt32
  /-- CSR offsets: predecessors of state `s` occupy offsets `[s, s + 1)`. -/
  predecessorOffsets : Array Nat
  /-- Legal predecessors, ascending inside every state bucket. -/
  predecessors : Array UInt32

namespace ConstrainedHmm

/-- IEEE-754 bits of the noncanonical negative-zero cost. -/
private def negativeZeroBits : UInt64 := 0x8000000000000000

/-- Decoder costs are finite, nonnegative, and use positive zero. -/
@[inline] def isCanonicalCost (cost : Cost) : Bool :=
  let value := cost.toFloat
  value.isFinite && decide (0.0 ≤ value) && value.toBits != negativeZeroBits

/-- Validate one dense cost array while retaining its exact source position. -/
private def validateArrayCosts (costs : Array Cost)
    (error : Nat → Float → UInt64 → ConstrainedHmmCompileError) :
    Except ConstrainedHmmCompileError Unit := do
  for index in [0:costs.size] do
    let value := costs[index]!.toFloat
    unless isCanonicalCost costs[index]! do
      throw <| error index value value.toBits

/-- Select the lowest-key sparse-emission failure independently of hash iteration order. -/
private def validateEmissions (hmm : Hmm) : Except ConstrainedHmmCompileError Unit := do
  let mut first : Option (UInt64 × ConstrainedHmmCompileError) := none
  for (key, cost) in hmm.emit do
    let tag := (key >>> 32).toNat
    let cause :=
      if !(tag < hmm.nTags) then
        some (.emissionTagOutOfRange key tag hmm.nTags)
      else if !isCanonicalCost cost then
        let value := cost.toFloat
        some (.invalidEmissionCost key value value.toBits)
      else
        none
    match cause with
    | none => pure ()
    | some error =>
      match first with
      | none => first := some (key, error)
      | some (priorKey, _) =>
        if key < priorKey then
          first := some (key, error)
  match first with
  | some (_, error) => throw error
  | none => pure ()

/-- Validate unique labels, find `O`, and reject unreachable orphan `I-TYPE` states. -/
private def validateInventory (tags : Array Bio.Tag) :
    Except ConstrainedHmmCompileError UInt32 := do
  let mut seen : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity tags.size
  let mut begins : Std.HashMap String Unit := {}
  let mut inside : Array (Nat × String) := #[]
  let mut outside : Option UInt32 := none
  for index in [0:tags.size] do
    let tag := tags.getD index .outside
    let label := tag.render
    match seen.get? label with
    | some first => throw <| .duplicateTag first index label
    | none => seen := seen.insert label index
    match tag with
    | .outside => outside := some (UInt32.ofNat index)
    | .begin entity => begins := begins.insert entity.name ()
    | .inside entity => inside := inside.push (index, entity.name)
  for (index, entity) in inside do
    unless begins.contains entity do
      throw <| .orphanInside index entity
  match outside with
  | some state => return state
  | none => throw .missingOutside

/-- Compile legal starts and one ascending predecessor bucket per next state. -/
private def compileIndex (tags : Array Bio.Tag) :
    Array UInt32 × Array Nat × Array UInt32 := Id.run do
  let mut starts : Array UInt32 := #[]
  for state in [0:tags.size] do
    if (tags.getD state .outside).legalStart then
      starts := starts.push (UInt32.ofNat state)
  let mut offsets : Array Nat := #[0]
  let mut predecessors : Array UInt32 := #[]
  for next in [0:tags.size] do
    for prior in [0:tags.size] do
      if Bio.Tag.legalTransition (tags.getD prior .outside) (tags.getD next .outside) then
        predecessors := predecessors.push (UInt32.ofNat prior)
    offsets := offsets.push predecessors.size
  return (starts, offsets, predecessors)

/-- Validate an HMM and compile its BIO2 transition constraints. -/
def compile (hmm : Hmm) (tags : Array Bio.Tag) :
    Except ConstrainedHmmCompileError ConstrainedHmm := do
  unless tags.size ≤ UInt32.size do
    throw <| .stateCapacity tags.size
  unless hmm.start.size = hmm.nTags && hmm.trans.size = hmm.nTags * hmm.nTags &&
      hmm.unk.size = hmm.nTags do
    throw <| .invalidDimensions hmm.nTags hmm.start.size hmm.trans.size hmm.unk.size
  unless tags.size = hmm.nTags do
    throw <| .invalidTagCount hmm.nTags tags.size
  let outside ← validateInventory tags
  validateArrayCosts hmm.start .invalidStartCost
  validateArrayCosts hmm.trans .invalidTransitionCost
  validateArrayCosts hmm.unk .invalidUnknownCost
  validateEmissions hmm
  let (startStates, predecessorOffsets, predecessors) := compileIndex tags
  return ⟨hmm, tags, outside, startStates, predecessorOffsets, predecessors⟩

/-- Number of compiled BIO2 states. -/
@[inline] def nStates (model : ConstrainedHmm) : Nat :=
  model.tags.size

/-- Materialize one state's ascending legal-predecessor bucket for inspection. -/
def predecessorsFor (model : ConstrainedHmm) (next : Nat) : Array UInt32 :=
  let start := model.predecessorOffsets.getD next 0
  let stop := model.predecessorOffsets.getD (next + 1) start
  model.predecessors.extract start stop

/-- Normalized length of the checked half-open word range `[start, stop)`. -/
def rangeLength (words : Array Tok) (start stop : Nat) : Nat :=
  let upper := min stop words.size
  upper - min start upper

/-- One constrained decoding result with its selected operational floating-point cost. -/
structure DecodeResult where
  cost : Cost
  tags : Array Nat
deriving Inhabited, Repr

/-- One flat-backpointer reconstruction step. -/
@[inline] private def backtraceStep (length nStates : Nat) (backs : Array UInt32)
    (fallback : UInt32) (state : Array Nat × UInt32) (offset : Nat) :
    Array Nat × UInt32 :=
  let position := length - 1 - offset
  let previous := backs.getD ((position - 1) * nStates + state.2.toNat) fallback
  (state.1.set! (position - 1) previous.toNat, previous)

/-- Reconstruct a path from flat row-major `UInt32` predecessor storage. -/
def backtrace (length nStates : Nat) (backs : Array UInt32) (best fallback : UInt32) :
    Array Nat :=
  if length = 0 then
    #[]
  else
    let initial := ((Array.replicate length fallback.toNat).set! (length - 1) best.toNat, best)
    ((List.range (length - 1)).foldl
      (backtraceStep length nStates backs fallback) initial).1

private theorem foldl_fst_size {Item Value State : Type} (items : List Item)
    (step : Array Value × State → Item → Array Value × State)
    (preserves : ∀ state item, (step state item).1.size = state.1.size)
    (initial : Array Value × State) :
    (items.foldl step initial).1.size = initial.1.size := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, preserves]

/-- Flat backtracing always returns exactly the requested number of states. -/
@[simp] theorem backtrace_size (length nStates : Nat) (backs : Array UInt32)
    (best fallback : UInt32) :
    (backtrace length nStates backs best fallback).size = length := by
  rw [backtrace]
  split
  · simp_all
  · rw [foldl_fst_size]
    · simp
    · intro state offset
      simp [backtraceStep]

/-- Internal sweep result before flat backpointer reconstruction. -/
private structure SweepResult where
  cost : Cost
  backs : Array UInt32
  best : UInt32

/-- Run the compiled constrained recurrence on a known nonempty normalized range. -/
private def sweepRange (model : ConstrainedHmm) (words : Array Tok)
    (start length : Nat) : SweepResult := Id.run do
  let nStates := model.nStates
  let firstWord := words.getD start 0
  let mut scores := Array.replicate nStates (0 : Cost)
  let mut reachable := Array.replicate nStates false
  for stateId in model.startStates do
    let state := stateId.toNat
    let score := model.hmm.startCost state * model.hmm.emissionCost state firstWord
    scores := scores.set! state score
    reachable := reachable.set! state true
  let mut backs : Array UInt32 := #[]
  for position in [1:length] do
    let previousScores := scores
    let previousReachable := reachable
    let word := words.getD (start + position) 0
    let mut nextScores := Array.replicate nStates (0 : Cost)
    let mut nextReachable := Array.replicate nStates false
    let mut nextBack := Array.replicate nStates model.outside
    for next in [0:nStates] do
      let bucketStart := model.predecessorOffsets.getD next 0
      let bucketStop := model.predecessorOffsets.getD (next + 1) bucketStart
      let emission := model.hmm.emissionCost next word
      let mut found := false
      let mut bestPrior := model.outside
      let mut best := (0 : Cost)
      for offset in [bucketStart:bucketStop] do
        let prior := (model.predecessors.getD offset model.outside).toNat
        if previousReachable.getD prior false then
          let candidate := previousScores.getD prior 0 *
            model.hmm.transitionCost prior next * emission
          if !found || candidate.toFloat < best.toFloat then
            found := true
            bestPrior := UInt32.ofNat prior
            best := candidate
      if found then
        nextScores := nextScores.set! next best
        nextReachable := nextReachable.set! next true
        nextBack := nextBack.set! next bestPrior
    scores := nextScores
    reachable := nextReachable
    for prior in nextBack do
      backs := backs.push prior
  let mut found := false
  let mut bestState := model.outside
  let mut bestCost := (0 : Cost)
  for state in [0:nStates] do
    if reachable.getD state false then
      let candidate := scores.getD state 0
      if !found || candidate.toFloat < bestCost.toFloat then
        found := true
        bestState := UInt32.ofNat state
        bestCost := candidate
  return ⟨bestCost, backs, bestState⟩

/-- Decode a normalized half-open range without allocating a word slice. -/
def decodeRangeResult (model : ConstrainedHmm) (words : Array Tok) (start stop : Nat) :
    DecodeResult :=
  let upper := min stop words.size
  let lower := min start upper
  let length := upper - lower
  if length = 0 then
    ⟨1, #[]⟩
  else
    let sweep := sweepRange model words lower length
    ⟨sweep.cost, backtrace length model.nStates sweep.backs sweep.best model.outside⟩

/-- Decode a half-open range and return only its dense BIO2 state ordinals. -/
@[inline] def decodeRange (model : ConstrainedHmm) (words : Array Tok)
    (start stop : Nat) : Array Nat :=
  (model.decodeRangeResult words start stop).tags

/-- Decode a complete observation sequence and retain its operational cost. -/
@[inline] def decodeResult (model : ConstrainedHmm) (words : Array Tok) : DecodeResult :=
  model.decodeRangeResult words 0 words.size

/-- Decode a complete observation sequence into dense BIO2 state ordinals. -/
@[inline] def decode (model : ConstrainedHmm) (words : Array Tok) : Array Nat :=
  model.decodeRange words 0 words.size

/-- Range decoding returns exactly the normalized requested number of positions. -/
@[simp] theorem decodeRange_size (model : ConstrainedHmm) (words : Array Tok)
    (start stop : Nat) :
    (model.decodeRange words start stop).size = rangeLength words start stop := by
  simp only [decodeRange, decodeRangeResult, rangeLength]
  split <;> simp_all

/-- An in-bounds ordered range decodes to its exact half-open width. -/
theorem decodeRange_size_of_bounds (model : ConstrainedHmm) (words : Array Tok)
    (start stop : Nat) (ordered : start ≤ stop) (inBounds : stop ≤ words.size) :
    (model.decodeRange words start stop).size = stop - start := by
  rw [decodeRange_size]
  simp [rangeLength, Nat.min_eq_left inBounds, Nat.min_eq_left ordered]

/-- Complete decoding produces exactly one BIO2 state per observation. -/
@[simp] theorem decode_size (model : ConstrainedHmm) (words : Array Tok) :
    (model.decode words).size = words.size := by
  simpa [decode] using
    model.decodeRange_size_of_bounds words 0 words.size (Nat.zero_le _) (Nat.le_refl _)

end ConstrainedHmm

end Nlp.Sequence
