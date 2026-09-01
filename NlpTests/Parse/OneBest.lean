import Nlp.Core.Score.NatCost
import Nlp.Core.Score.Vit
import Nlp.Parse.OneBest

/-!
Tests for one-best extraction over the ambiguous grammar G₁ (the grammar of
`NlpTests/Parse/CKY.lean`, copied here because its definitions are private).  The exact `NatCost`
carrier gates the equality assertions; `Vit` gets a tolerance-only smoke test.
-/

namespace NlpTests.Parse.OneBest

open Nlp
open Nlp.Parse

private def sentence : Array Tok := #[0, 1, 2, 3, 4]

/-- Strict min-plus improvement: a finite candidate beats `+∞` and any strictly larger cost. -/
private def costBetter (a b : NatCost) : Bool :=
  match a.toOption, b.toOption with
  | some x, some y => x < y
  | some _, none => true
  | none, _ => false

/-- G₁ with exact min-plus costs.  Nonterminals: S=0, NP=1, VP=2, PP=3, V=4, P=5.  The
low-attachment derivation costs 10, the high-attachment one 11, so the one-best is unique. -/
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

/-- The extracted one-best tree under exact costs, shared by the assertions below. -/
private def natBest : Option Tree := oneBestTree costBetter natGrammar sentence

/-- The one-best value chart coincides with the `ckyNaive` oracle chart. -/
example : (ckyOneBest costBetter natGrammar sentence).1 = ckyNaive natGrammar sentence := by
  native_decide

/-- (a) Extraction succeeds on the ambiguous 5-word sentence. -/
example : natBest.isSome = true := by native_decide

/-- (b) The extracted tree re-scores to exactly the chart goal value. -/
example : natBest.bind (treeScore natGrammar) = some (ckyNaiveGoal natGrammar sentence) := by
  native_decide

/-- The goal value is the low-attachment cost 10, not the high-attachment 11. -/
example : ckyNaiveGoal natGrammar sentence = NatCost.fin 10 := by native_decide

/-- (c) The extracted tree yields exactly the five input words. -/
example : natBest.map Tree.width = some 5 := by native_decide

/-- The extracted terminal yield is the input sentence, in order. -/
example : natBest.map Tree.yieldWords = some sentence := by native_decide

/-- A rejected sentence extracts no tree. -/
example : (oneBestTree costBetter natGrammar #[0, 99]).isNone = true := by native_decide

/-- The empty sentence extracts no tree. -/
example : (oneBestTree costBetter natGrammar #[]).isNone = true := by native_decide

/-- Strict max-times improvement over `Vit` scores. -/
private def vitBetter (a b : Vit) : Bool := b.toFloat < a.toFloat

/-- G₁ with `Vit` weights, copied from `NlpTests/Parse/CKY.lean`; best score 0.0252. -/
private def vitGrammar : CNF Vit :=
  { bin :=
      #[ ⟨0, 1, 2, ⟨1.0⟩⟩,
         ⟨2, 4, 1, ⟨0.7⟩⟩,
         ⟨2, 2, 3, ⟨0.3⟩⟩,
         ⟨1, 1, 3, ⟨0.4⟩⟩,
         ⟨3, 5, 1, ⟨1.0⟩⟩ ]
    lex :=
      #[ ⟨1, 0, ⟨1.0⟩⟩,
         ⟨4, 1, ⟨1.0⟩⟩,
         ⟨1, 2, ⟨0.3⟩⟩,
         ⟨5, 3, ⟨1.0⟩⟩,
         ⟨1, 4, ⟨0.3⟩⟩ ]
    start := 0
    nNT := 6 }

/-- `Vit` smoke test: extraction succeeds and the re-scored tree matches within tolerance. -/
example :
    ((oneBestTree vitBetter vitGrammar sentence).bind (treeScore vitGrammar)).map
        (fun s ↦ decide (Float.abs (s.toFloat - 0.0252) < 1e-12)) = some true := by
  native_decide

end NlpTests.Parse.OneBest
