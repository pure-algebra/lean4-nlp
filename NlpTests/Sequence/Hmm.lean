import Nlp.Sequence.Hmm

namespace NlpTests.Sequence.Hmm

open Nlp Nlp.Sequence

private def cost (value : Float) : Cost := ⟨value⟩

private def tinyEmissions : Std.HashMap UInt64 Cost :=
  ({} : Std.HashMap UInt64 Cost)
    |>.insert (Nlp.Sequence.Hmm.emissionKey 0 10) (cost 0.0)
    |>.insert (Nlp.Sequence.Hmm.emissionKey 1 10) (cost 5.0)
    |>.insert (Nlp.Sequence.Hmm.emissionKey 0 11) (cost 5.0)
    |>.insert (Nlp.Sequence.Hmm.emissionKey 1 11) (cost 0.0)

private def tiny : Nlp.Sequence.Hmm where
  nTags := 2
  start := #[cost 0.0, cost 10.0]
  trans := #[cost 5.0, cost 0.0, cost 5.0, cost 0.0]
  emit := tinyEmissions
  unk := #[cost 20.0, cost 20.0]

#guard tiny.decode #[10, 11, 11] == #[0, 1, 1]

private def tied : Nlp.Sequence.Hmm where
  nTags := 2
  start := #[cost 0.0, cost 0.0]
  trans := Array.replicate 4 (cost 0.0)
  emit := {}
  unk := #[cost 0.0, cost 0.0]

/- Exact ties choose the first prior and first final tag. -/
#guard tied.decode #[10, 11, 12] == #[0, 0, 0]

private def malformed : Nlp.Sequence.Hmm where
  nTags := 2
  start := #[]
  trans := #[]
  emit := {}
  unk := #[]

#guard malformed.decode #[10, 11] == #[0, 0]
#guard tiny.decode #[] == #[]
#guard ({ malformed with nTags := 0 }).decode #[10] == #[]

private def training : Array (Array (Tok × Nat)) :=
  #[#[(10, 0), (11, 1)], #[(10, 0), (10, 0)], #[], #[(12, 7)]]

private def estimated : Nlp.Sequence.Hmm :=
  Nlp.Sequence.Hmm.estimate training 2 1.0

private def estimateShape : Bool :=
  estimated.start.size == 2 && estimated.trans.size == 4 && estimated.unk.size == 2 &&
    estimated.emit.size == 2 && estimated.start.all (fun value ↦ value.toFloat.isFinite) &&
    estimated.trans.all (fun value ↦ value.toFloat.isFinite) &&
    estimated.unk.all (fun value ↦ value.toFloat.isFinite)

#guard estimateShape

private def knownEmissionIsCheaper : Bool :=
  if (estimated.emissionCost 0 10).toFloat < (estimated.emissionCost 0 99).toFloat then
    true
  else
    false

#guard knownEmissionIsCheaper

private def chainLayout : Bool :=
  let chain := tiny.toChain #[10, 11]
  chain.len == 2 && chain.nS == 2 &&
    (chain.init 0).toFloat.toBits == (cost 0.0).toFloat.toBits &&
    (chain.arc 1 0 1).toFloat.toBits == (cost 0.0).toFloat.toBits

#guard chainLayout

private def pathCost (model : Nlp.Sequence.Hmm) (words : Array Tok)
    (tags : Array Nat) : Cost := Id.run do
  if words.isEmpty || words.size != tags.size then
    return 0
  let chain := model.toChain words
  let mut total := chain.init (tags.getD 0 chain.nS)
  for position in [1:words.size] do
    let prior := tags.getD (position - 1) chain.nS
    let next := tags.getD position chain.nS
    total := total * chain.arc position prior next
  return total * chain.fin (tags.getD (words.size - 1) chain.nS)

private def decodeAgreesWithForward (model : Nlp.Sequence.Hmm)
    (words : Array Tok) : Bool :=
  let decoded := model.decode words
  (pathCost model words decoded).toFloat.toBits == (model.toChain words).forward.toFloat.toBits

#guard decodeAgreesWithForward tiny #[10, 11, 11]
#guard decodeAgreesWithForward tied #[10, 11, 12]
#guard decodeAgreesWithForward estimated #[10, 11, 10]

private def constrainedArc : Bool :=
  let chain := (tied.toChain #[10, 11]).constrain fun prior next ↦ prior == next
  (chain.arc 1 0 0).toFloat.isFinite && !(chain.arc 1 0 1).toFloat.isFinite

#guard constrainedArc

end NlpTests.Sequence.Hmm
