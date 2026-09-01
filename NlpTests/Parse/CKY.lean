import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog
import Nlp.Core.Score.Vit
import Nlp.Parse.CKY
import Nlp.Parse.CKYLemmas

namespace NlpTests.Parse.CKY

open Nlp
open Nlp.Parse

private def sentence : Array Tok := #[0, 1, 2, 3, 4]

/-! A compact ambiguous attachment grammar with nonterminals
    S=0, NP=1, VP=2, PP=3, V=4, and P=5. -/

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

private def grammarWithOutOfBoundsIds : CNF Count :=
  { countGrammar with
    bin := countGrammar.bin.push ⟨0, 99, 0, 1⟩
    lex := countGrammar.lex.push ⟨99, 0, 1⟩ }

example :
    cky grammarWithOutOfBoundsIds sentence =
      ckyNaive grammarWithOutOfBoundsIds sentence := by
  native_decide

/-! The proved lexical-layer characterization instantiates at the test grammar, and the
characterized cell value matches direct evaluation. -/

example :
    (ckyNaive countGrammar sentence).getD (Chart.cidx 5 6 0 1 1) 0 =
      lexCellSum countGrammar sentence 0 1 :=
  ckyNaive_getD_lex countGrammar sentence 0 1 (by decide) (by decide)

example : (lexCellSum countGrammar sentence 0 1).toNat = 1 := by native_decide

/-- The binary Bellman characterization instantiates at the goal cell of the test grammar. -/
example :
    (ckyNaive countGrammar sentence).getD (Chart.cidx 5 6 0 5 0) 0 =
      binCellSum countGrammar sentence (ckyNaive countGrammar sentence) 0 5 0 :=
  ckyNaive_getD_bin countGrammar sentence 0 5 0 (by omega) (by decide) (by decide)

/-- The characterized goal-cell value agrees with direct evaluation: two parses. -/
example :
    (binCellSum countGrammar sentence (ckyNaive countGrammar sentence) 0 5 0).toNat = 2 := by
  native_decide

end NlpTests.Parse.CKY
