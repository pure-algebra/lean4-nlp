import Std.Data.HashMap
import Nlp.Core.Score.Cost
import Nlp.Grammar.CFG
import Nlp.Sequence.Chain

/-!
# Bigram hidden Markov models

The model stores negative-log costs and projects directly into the existing min-plus `Chain`
engine. Estimation uses add-k smoothing. Decoding keeps values and backpointers separate and is
left-biased on exact ties, so repeated runs are deterministic.
-/

namespace Nlp
namespace Sequence

/-- A bigram HMM over interned words and dense tags. -/
structure Hmm where
  nTags : Nat
  start : Array Cost
  trans : Array Cost
  emit : Std.HashMap UInt64 Cost
  unk : Array Cost
deriving Inhabited

namespace Hmm

/-- Pack a dense tag and an interned word into one emission-table key. -/
@[inline] def emissionKey (tag : Nat) (word : Tok) : UInt64 :=
  (UInt64.ofNat tag <<< 32) ||| word.toUInt64

/-- Invalid smoothing values fall back to Laplace smoothing. -/
@[inline] def checkedAddK (addK : Float) : Float :=
  if addK.isFinite then
    if 0.0 < addK then addK else 1.0
  else
    1.0

@[inline] private def negativeLogRatio (numerator denominator : Float) : Cost :=
  ⟨-(Float.log (numerator / denominator))⟩

@[inline] private def countFloat (count : Nat) : Float :=
  Float.ofNat count

/-- Read a start cost, treating a malformed short array as unreachable. -/
@[inline] def startCost (model : Hmm) (tag : Nat) : Cost :=
  model.start.getD tag 0

/-- Read a row-major transition cost, treating malformed storage as unreachable. -/
@[inline] def transitionCost (model : Hmm) (prior next : Nat) : Cost :=
  model.trans.getD (prior * model.nTags + next) 0

/-- Read an emission cost, falling back to the tag's unknown-word cost. -/
@[inline] def emissionCost (model : Hmm) (tag : Nat) (word : Tok) : Cost :=
  model.emit.getD (emissionKey tag word) (model.unk.getD tag 0)

/--
Estimate a smoothed bigram HMM from tagged sentences.

Observations whose tag is outside `0 .. nTags - 1` are ignored. Start and transition rows use
add-k smoothing over tags. Emissions use a shared observed vocabulary plus one unknown bucket.
-/
def estimate (sentences : Array (Array (Tok × Nat))) (nTags : Nat)
    (addK : Float := 1.0) : Hmm := Id.run do
  let smoothing := checkedAddK addK
  let mut startCounts := Array.replicate nTags 0
  let mut transCounts := Array.replicate (nTags * nTags) 0
  let mut outgoingCounts := Array.replicate nTags 0
  let mut tagCounts := Array.replicate nTags 0
  let mut validStarts := 0
  let mut emissionCounts : Std.HashMap UInt64 Nat := {}
  let mut observed : Array (UInt64 × Nat) := #[]
  let mut vocabulary : Std.HashMap Tok Unit := {}
  for sentence in sentences do
    match sentence[0]? with
    | some (_, tag) =>
        if tag < nTags then
          startCounts := startCounts.set! tag (startCounts.getD tag 0 + 1)
          validStarts := validStarts + 1
    | none => pure ()
    for position in [0:sentence.size] do
      let (word, tag) := sentence.getD position (0, nTags)
      if tag < nTags then
        tagCounts := tagCounts.set! tag (tagCounts.getD tag 0 + 1)
        vocabulary := vocabulary.insert word ()
        let key := emissionKey tag word
        let oldCount := emissionCounts.getD key 0
        if oldCount == 0 then
          observed := observed.push (key, tag)
        emissionCounts := emissionCounts.insert key (oldCount + 1)
      if 0 < position then
        let (_, prior) := sentence.getD (position - 1) (0, nTags)
        if prior < nTags && tag < nTags then
          let index := prior * nTags + tag
          transCounts := transCounts.set! index (transCounts.getD index 0 + 1)
          outgoingCounts := outgoingCounts.set! prior (outgoingCounts.getD prior 0 + 1)
  let startDenominator := countFloat validStarts + smoothing * countFloat nTags
  let start := Array.ofFn (n := nTags) fun tag ↦
    negativeLogRatio (countFloat (startCounts.getD tag.val 0) + smoothing)
      startDenominator
  let trans := Array.ofFn (n := nTags * nTags) fun index ↦
    let prior := index.val / nTags
    let denominator := countFloat (outgoingCounts.getD prior 0) +
      smoothing * countFloat nTags
    negativeLogRatio (countFloat (transCounts.getD index.val 0) + smoothing) denominator
  let vocabularyBuckets := vocabulary.size + 1
  let unk := Array.ofFn (n := nTags) fun tag ↦
    let denominator := countFloat (tagCounts.getD tag.val 0) +
      smoothing * countFloat vocabularyBuckets
    negativeLogRatio smoothing denominator
  let mut emit : Std.HashMap UInt64 Cost := {}
  for keyAndTag in observed do
    let (key, tag) := keyAndTag
    let denominator := countFloat (tagCounts.getD tag 0) +
      smoothing * countFloat vocabularyBuckets
    let numerator := countFloat (emissionCounts.getD key 0) + smoothing
    emit := emit.insert key (negativeLogRatio numerator denominator)
  return ⟨nTags, start, trans, emit, unk⟩

/-- Project an HMM and a word sequence into the semiring-generic chain engine. -/
def toChain (model : Hmm) (words : Array Tok) : Chain Cost where
  len := words.size
  nS := model.nTags
  init := fun tag ↦
    match words[0]? with
    | some word => model.startCost tag * model.emissionCost tag word
    | none => 0
  arc := fun position prior next ↦
    match words[position]? with
    | some word => model.transitionCost prior next * model.emissionCost next word
    | none => 0
  fin := fun _ ↦ 1

/-- One right-to-left backtrace step, carrying the partially reconstructed path and tag. -/
@[inline] def backtraceStep (length : Nat) (backs : Array (Array Nat))
    (state : Array Nat × Nat) (offset : Nat) : Array Nat × Nat :=
  let position := length - 1 - offset
  let previous := (backs.getD (position - 1) #[]).getD state.2 0
  (state.1.set! (position - 1) previous, previous)

/-- Reconstruct a path from one predecessor array per position after the first. -/
def backtrace (length : Nat) (backs : Array (Array Nat)) (bestTag : Nat) : Array Nat :=
  let initial := ((Array.replicate length 0).set! (length - 1) bestTag, bestTag)
  let result := (List.range (length - 1)).foldl (backtraceStep length backs) initial
  result.1

/--
Decode the leftmost minimum-cost tag path.

Empty input and zero-state models return an empty path. Short model arrays are read as infinity,
so malformed public values cannot cause an out-of-bounds failure.
-/
def decode (model : Hmm) (words : Array Tok) : Array Nat := Id.run do
  if words.isEmpty || model.nTags == 0 then
    return #[]
  let firstWord := words.getD 0 0
  let mut scores := Array.ofFn (n := model.nTags) fun tag ↦
    model.startCost tag.val * model.emissionCost tag.val firstWord
  let mut backs : Array (Array Nat) := #[]
  for position in [1:words.size] do
    let previous := scores
    let word := words.getD position 0
    let mut nextScores := Array.replicate model.nTags (0 : Cost)
    let mut nextBack := Array.replicate model.nTags 0
    for next in [0:model.nTags] do
      let emission := model.emissionCost next word
      let firstArc := model.transitionCost 0 next * emission
      let mut bestPrior := 0
      let mut best := previous.getD 0 0 * firstArc
      for prior in [1:model.nTags] do
        let arc := model.transitionCost prior next * emission
        let candidate := previous.getD prior 0 * arc
        if candidate.toFloat < best.toFloat then
          best := candidate
          bestPrior := prior
      nextScores := nextScores.set! next best
      nextBack := nextBack.set! next bestPrior
    scores := nextScores
    backs := backs.push nextBack
  let mut bestTag := 0
  let mut bestFinal := scores.getD 0 0
  for tag in [1:model.nTags] do
    let candidate := scores.getD tag 0
    if candidate.toFloat < bestFinal.toFloat then
      bestFinal := candidate
      bestTag := tag
  return backtrace words.size backs bestTag

end Hmm

end Sequence

namespace Chain

/-- Replace illegal state-to-state transitions by the semiring zero. -/
def constrain {K : Type u} [Zero K] (chain : Chain K)
    (legal : Nat → Nat → Bool) : Chain K :=
  { chain with
    arc := fun position prior next ↦
      if legal prior next then chain.arc position prior next else 0 }

end Chain
end Nlp
