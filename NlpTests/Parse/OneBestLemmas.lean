import Nlp.Core.Score.NatCost
import Nlp.Parse.OneBestLemmas

/-!
Instantiation checks for the VIT-1 oracle equation `Parse.ckyOneBest_fst`: the equalities that
`NlpTests/Parse/OneBest.lean` asserts with `native_decide` follow definitionally from the
theorem, at a concrete exact carrier and for arbitrary inputs.
-/

namespace NlpTests.Parse.OneBestLemmas

open Nlp
open Nlp.Parse

/-- The theorem is carrier- and predicate-generic; no laws about `better` are needed. -/
example {K : Type} [SemiringOps K] [Inhabited K] (better : K → K → Bool)
    (grammar : CNF K) (words : Array Tok) :
    (ckyOneBest better grammar words).1 = ckyNaive grammar words :=
  ckyOneBest_fst better grammar words

private def sentence : Array Tok := #[0, 1, 2, 3, 4]

/-- Strict min-plus improvement, as in `NlpTests/Parse/OneBest.lean`. -/
private def costBetter (a b : NatCost) : Bool :=
  match a.toOption, b.toOption with
  | some x, some y => x < y
  | some _, none => true
  | none, _ => false

/-- G₁ with exact min-plus costs, copied from `NlpTests/Parse/OneBest.lean`. -/
private def natGrammar : CNF NatCost :=
  { bin :=
      #[ ⟨0, 1, 2, NatCost.fin 1⟩,
         ⟨2, 4, 1, NatCost.fin 1⟩,
         ⟨2, 2, 3, NatCost.fin 3⟩,
         ⟨1, 1, 3, NatCost.fin 2⟩,
         ⟨3, 5, 1, NatCost.fin 1⟩ ]
    lex :=
      #[ ⟨1, 0, NatCost.fin 1⟩,
         ⟨4, 1, NatCost.fin 1⟩,
         ⟨1, 2, NatCost.fin 1⟩,
         ⟨5, 3, NatCost.fin 1⟩,
         ⟨1, 4, NatCost.fin 1⟩ ]
    start := 0
    nNT := 6 }

/-- The oracle equation of `NlpTests/Parse/OneBest.lean`, now a theorem instance rather than a
`native_decide` run. -/
example : (ckyOneBest costBetter natGrammar sentence).1 = ckyNaive natGrammar sentence :=
  ckyOneBest_fst costBetter natGrammar sentence

/-- Goal-value form, likewise for free. -/
example :
    (ckyOneBest costBetter natGrammar sentence).1.getD
        (goalIndex natGrammar sentence.size) 0 =
      ckyNaiveGoal natGrammar sentence :=
  ckyOneBest_fst_goal costBetter natGrammar sentence

end NlpTests.Parse.OneBestLemmas
