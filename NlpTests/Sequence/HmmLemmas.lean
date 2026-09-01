import Nlp.Sequence.HmmLemmas

namespace NlpTests.Sequence.HmmLemmas

open Nlp Nlp.Sequence

private def corpus : Array (Array (Tok × Nat)) :=
  #[#[(10, 0), (11, 1)], #[(10, 0)]]

/-- The estimator's dimensional contract is available without evaluating floating-point data. -/
example : (Nlp.Sequence.Hmm.estimate corpus 2).WF :=
  Nlp.Sequence.Hmm.estimate_wf corpus 2 1.0

/-- Backtrace storage cannot change the requested output length. -/
example (backs : Array (Array Nat)) (tag : Nat) :
    (Nlp.Sequence.Hmm.backtrace 7 backs tag).size = 7 :=
  Nlp.Sequence.Hmm.backtrace_size 7 backs tag

/-- The decoder's nondegenerate branch returns one tag per observation. -/
example (model : Nlp.Sequence.Hmm) (words : Array Tok)
    (nonempty : words.isEmpty = false) (positiveTags : 0 < model.nTags) :
    (model.decode words).size = words.size :=
  Nlp.Sequence.Hmm.decode_size_of_nonempty model words nonempty positiveTags

/-- The unconditional decoder size theorem exposes both total fallback branches. -/
example (model : Nlp.Sequence.Hmm) (words : Array Tok) :
    (model.decode words).size =
      if words.isEmpty || model.nTags == 0 then 0 else words.size :=
  Nlp.Sequence.Hmm.decode_size model words

/-- Constraint proofs expose legal transition behavior directly. -/
example (chain : Chain Nat) (position prior next : Nat) :
    (chain.constrain fun _ _ ↦ true).arc position prior next =
      chain.arc position prior next :=
  Chain.constrain_arc_of_true chain _ position prior next rfl

/-- Constraint proofs expose forbidden transition behavior directly. -/
example (chain : Chain Nat) (position prior next : Nat) :
    (chain.constrain fun _ _ ↦ false).arc position prior next = 0 :=
  Chain.constrain_arc_of_false chain _ position prior next rfl

end NlpTests.Sequence.HmmLemmas
