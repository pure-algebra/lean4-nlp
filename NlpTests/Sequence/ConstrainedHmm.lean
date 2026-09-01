import Nlp.Sequence.ConstrainedHmm

namespace NlpTests.Sequence.ConstrainedHmm

open Nlp Nlp.Sequence
open Nlp.Sequence.Bio

private def cost (value : Float) : Cost := ⟨value⟩

/-- A fixture helper whose fallback is unreachable for canonical labels. -/
private def parsed (label : String) : Tag :=
  match Tag.parse label with
  | .ok tag => tag
  | .error _ => .outside

private def labels : Array Tag :=
  #[parsed "O", parsed "B-PERSON", parsed "I-PERSON"]

private def tiny : Hmm where
  nTags := 3
  start := #[cost 5.0, cost 0.0, cost 0.0]
  trans := #[
    cost 1.0, cost 1.0, cost 0.0,
    cost 5.0, cost 5.0, cost 0.0,
    cost 5.0, cost 5.0, cost 0.0]
  emit := {}
  unk := #[cost 0.0, cost 0.0, cost 0.0]

private def compiled? :
    Except ConstrainedHmmCompileError Nlp.Sequence.ConstrainedHmm :=
  Nlp.Sequence.ConstrainedHmm.compile tiny labels

/-- Reconstruct a path for the deliberately dense reference implementation. -/
private def denseBacktrace (length nStates : Nat) (backs : Array UInt32)
    (best fallback : UInt32) : Array Nat := Id.run do
  if length = 0 then
    return #[]
  let mut output := (Array.replicate length fallback.toNat).set! (length - 1) best.toNat
  let mut current := best
  for offset in [0:length - 1] do
    let position := length - 1 - offset
    let previous := backs.getD ((position - 1) * nStates + current.toNat) fallback
    output := output.set! (position - 1) previous.toNat
    current := previous
  return output

/-- Dense masked oracle: scan every prior state, retaining explicit reachability. -/
private def denseDecode (model : Nlp.Sequence.ConstrainedHmm)
    (words : Array Tok) : Nlp.Sequence.ConstrainedHmm.DecodeResult := Id.run do
  if words.isEmpty then
    return ⟨1, #[]⟩
  let nStates := model.nStates
  let firstWord := words.getD 0 0
  let mut scores := Array.replicate nStates (0 : Cost)
  let mut reachable := Array.replicate nStates false
  for state in [0:nStates] do
    if (model.tags.getD state .outside).legalStart then
      let score := model.hmm.startCost state * model.hmm.emissionCost state firstWord
      scores := scores.set! state score
      reachable := reachable.set! state true
  let mut backs : Array UInt32 := #[]
  for position in [1:words.size] do
    let previousScores := scores
    let previousReachable := reachable
    let word := words.getD position 0
    let mut nextScores := Array.replicate nStates (0 : Cost)
    let mut nextReachable := Array.replicate nStates false
    let mut nextBack := Array.replicate nStates model.outside
    for next in [0:nStates] do
      let emission := model.hmm.emissionCost next word
      let mut found := false
      let mut bestPrior := model.outside
      let mut best := (0 : Cost)
      for prior in [0:nStates] do
        if Bio.Tag.legalTransition (model.tags.getD prior .outside)
            (model.tags.getD next .outside) && previousReachable.getD prior false then
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
  return ⟨bestCost, denseBacktrace words.size nStates backs bestState model.outside⟩

private def compileAndIndex : Bool :=
  match compiled? with
  | .error _ => false
  | .ok model =>
      model.outside == 0 && model.startStates == #[0, 1] &&
        model.predecessorsFor 0 == #[0, 1, 2] &&
        model.predecessorsFor 1 == #[0, 1, 2] &&
        model.predecessorsFor 2 == #[1, 2]

#guard compileAndIndex

private def twoTypeLabels : Array Tag :=
  #[parsed "O", parsed "B-PERSON", parsed "I-PERSON",
    parsed "B-ORGANIZATION", parsed "I-ORGANIZATION"]

private def twoTypeHmm : Hmm where
  nTags := 5
  start := Array.replicate 5 (cost 0.0)
  trans := Array.replicate 25 (cost 0.0)
  emit := {}
  unk := Array.replicate 5 (cost 0.0)

private def entitySpecificBuckets : Bool :=
  match Nlp.Sequence.ConstrainedHmm.compile twoTypeHmm twoTypeLabels with
  | .error _ => false
  | .ok model =>
      model.predecessorsFor 2 == #[1, 2] && model.predecessorsFor 4 == #[3, 4]

#guard entitySpecificBuckets

private def constrainedPath : Bool :=
  match compiled? with
  | .error _ => false
  | .ok model =>
      let decoded := model.decode #[10, 11]
      let decodedTags := decoded.map fun state ↦ model.tags.getD state .outside
      decoded == #[1, 2] && Tag.valid decodedTags

#guard constrainedPath

private def denseParity : Bool :=
  match compiled? with
  | .error _ => false
  | .ok model =>
      let words : Array Tok := #[10, 11, 12, 13]
      let indexed := model.decodeResult words
      let dense := denseDecode model words
      indexed.tags == dense.tags && indexed.cost.toFloat.toBits == dense.cost.toFloat.toBits

#guard denseParity

private def tied : Hmm where
  nTags := 3
  start := Array.replicate 3 (cost 0.0)
  trans := Array.replicate 9 (cost 0.0)
  emit := {}
  unk := Array.replicate 3 (cost 0.0)

private def leftBiasedTies : Bool :=
  match Nlp.Sequence.ConstrainedHmm.compile tied labels with
  | .error _ => false
  | .ok model => model.decode #[20, 21, 22] == #[0, 0, 0]

#guard leftBiasedTies

private def huge : Float := 1.0e308

private def overflowing : Hmm where
  nTags := 1
  start := #[cost huge]
  trans := #[cost huge]
  emit := {}
  unk := #[cost huge]

private def overflowRemainsReachable : Bool :=
  match Nlp.Sequence.ConstrainedHmm.compile overflowing #[parsed "O"] with
  | .error _ => false
  | .ok model =>
      let result := model.decodeResult #[30, 31, 32]
      result.tags == #[0, 0, 0] && !result.cost.toFloat.isFinite

#guard overflowRemainsReachable

private def rangeLengths : Bool :=
  match compiled? with
  | .error _ => false
  | .ok model =>
      let words : Array Tok := #[1, 2, 3, 4, 5]
      (model.decodeRange words 1 4).size == 3 &&
        (model.decodeRange words 3 99).size == 2 &&
        (model.decodeRange words 4 2).isEmpty

#guard rangeLengths

private def rejectsDimensions : Bool :=
  let malformed := { tiny with trans := #[] }
  match Nlp.Sequence.ConstrainedHmm.compile malformed labels with
  | .error (.invalidDimensions 3 3 0 3) => true
  | _ => false

#guard rejectsDimensions

private def rejectsTagCount : Bool :=
  match Nlp.Sequence.ConstrainedHmm.compile tiny #[parsed "O"] with
  | .error (.invalidTagCount 3 1) => true
  | _ => false

#guard rejectsTagCount

private def twoState : Hmm where
  nTags := 2
  start := Array.replicate 2 (cost 0.0)
  trans := Array.replicate 4 (cost 0.0)
  emit := {}
  unk := Array.replicate 2 (cost 0.0)

private def rejectsInventoryFailures : Bool :=
  let duplicate :=
    match Nlp.Sequence.ConstrainedHmm.compile twoState #[parsed "O", parsed "O"] with
    | .error (.duplicateTag 0 1 "O") => true
    | _ => false
  let missing :=
    match Nlp.Sequence.ConstrainedHmm.compile twoState
        #[parsed "B-PERSON", parsed "I-PERSON"] with
    | .error .missingOutside => true
    | _ => false
  let orphan :=
    match Nlp.Sequence.ConstrainedHmm.compile twoState #[parsed "O", parsed "I-PERSON"] with
    | .error (.orphanInside 1 "PERSON") => true
    | _ => false
  duplicate && missing && orphan

#guard rejectsInventoryFailures

private def rejectsInvalidCosts : Bool :=
  let malformed := { tiny with start := #[cost (-1.0), cost 0.0, cost 0.0] }
  match Nlp.Sequence.ConstrainedHmm.compile malformed labels with
  | .error (.invalidStartCost 0 value bits) =>
      value.toBits == (-1.0 : Float).toBits && bits == value.toBits
  | _ => false

#guard rejectsInvalidCosts

/-- The public range theorem exposes exact output length without evaluating the decoder. -/
example (model : Nlp.Sequence.ConstrainedHmm) (words : Array Tok)
    (start stop : Nat) (ordered : start ≤ stop) (inBounds : stop ≤ words.size) :
    (model.decodeRange words start stop).size = stop - start :=
  model.decodeRange_size_of_bounds words start stop ordered inBounds

/-- Complete constrained decoding is length preserving because the compiled `O` path is total. -/
example (model : Nlp.Sequence.ConstrainedHmm) (words : Array Tok) :
    (model.decode words).size = words.size :=
  model.decode_size words

end NlpTests.Sequence.ConstrainedHmm
