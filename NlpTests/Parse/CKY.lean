import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog
import Nlp.Core.Score.Vit
import Nlp.Parse.CKY

namespace NlpTests.Parse.CKY

open Nlp
open Nlp.Parse

private def sentence : Array Tok := #[0, 1, 2, 3, 4]

/-! The ambiguous grammar G₁ from `reference/deduction-rules.md` §7.1.
    Nonterminals: S=0, NP=1, VP=2, PP=3, V=4, P=5. -/

private def countGrammar : CNF Count :=
  { bin :=
      #[ ⟨0, 1, 2, 1⟩,
         ⟨2, 4, 1, 1⟩,
         ⟨2, 2, 3, 1⟩,
         ⟨1, 1, 3, 1⟩,
         ⟨3, 5, 1, 1⟩ ]
    lex :=
      #[ ⟨1, 0, 1⟩,
         ⟨4, 1, 1⟩,
         ⟨1, 2, 1⟩,
         ⟨5, 3, 1⟩,
         ⟨1, 4, 1⟩ ]
    start := 0
    nNT := 6 }

example : (ckyNaiveGoal countGrammar sentence).toNat = 2 := by native_decide

example : cky countGrammar sentence = ckyNaive countGrammar sentence := by native_decide

example : (ckyGoal countGrammar sentence).toNat = 2 := by native_decide

private def recogGrammar : CNF Recog :=
  { bin := countGrammar.bin.map (fun rule =>
      ⟨rule.lhs, rule.r1, rule.r2, 1⟩)
    lex := countGrammar.lex.map (fun rule => ⟨rule.lhs, rule.tok, 1⟩)
    start := countGrammar.start
    nNT := countGrammar.nNT }

example : (ckyNaiveGoal recogGrammar sentence).toBool = true := by native_decide

example : cky recogGrammar sentence = ckyNaive recogGrammar sentence := by native_decide

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

/-- The low-attachment derivation is Viterbi-best with score 0.0252. -/
example : Float.abs ((ckyNaiveGoal vitGrammar sentence).toFloat - 0.0252) < 1e-12 := by
  native_decide

private def rejectedSentence : Array Tok := #[0, 99]

example : (ckyNaiveGoal recogGrammar rejectedSentence).toBool = false := by native_decide

example : cky recogGrammar rejectedSentence = ckyNaive recogGrammar rejectedSentence := by
  native_decide

private def lexicalOnly : CNF Count :=
  { bin := #[]
    lex := #[⟨0, 7, 1⟩, ⟨0, 7, 1⟩]
    start := 0
    nNT := 1 }

example : cky lexicalOnly #[7] = ckyNaive lexicalOnly #[7] := by native_decide
example : (ckyGoal lexicalOnly #[7]).toNat = 2 := by native_decide

example : cky countGrammar #[] = ckyNaive countGrammar #[] := by native_decide

end NlpTests.Parse.CKY
