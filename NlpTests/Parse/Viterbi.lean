import Nlp.Parse.OneBest
import Nlp.Parse.Viterbi

namespace NlpTests.Parse.Viterbi

open Nlp
open Nlp.Parse

private def sentence : Array Tok := #[0, 1, 2, 3, 4]

/-! The ambiguous G₁ grammar from `reference/deduction-rules.md` §7.1.
    Nonterminals: S=0, NP=1, VP=2, PP=3, V=4, P=5. -/
private def grammar : CNF Vit :=
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

private def indexed := grammar.index
private def chart := Nlp.Parse.Viterbi.ckyVit indexed sentence
private def chartGoal : Vit :=
  chart.score.getD (goalIndex grammar sentence.size) 0
private def tree := Nlp.Parse.Viterbi.extractTree indexed sentence chart

/-- On canonical finite `[0, 1]` weights, provenance CKY matches the values-only oracle bits. -/
example : chartGoal.toFloat.toBits = (ckyNaiveGoal grammar sentence).toFloat.toBits := by
  native_decide

example : Float.abs (chartGoal.toFloat - 0.0252) < 1e-12 := by native_decide

example : tree.map Tree.yieldWords = some sentence := by native_decide
example : tree.map Tree.width = some sentence.size := by native_decide

private def spansWellFormed (parsed : Tree) (n : Nat) : Bool :=
  let spans := parsed.spans
  spans.all fun outer ↦
    outer.2.1 < outer.2.2 && outer.2.2 ≤ n && spans.all fun inner ↦
      outer.2.2 ≤ inner.2.1 || inner.2.2 ≤ outer.2.1 ||
        (outer.2.1 ≤ inner.2.1 && inner.2.2 ≤ outer.2.2) ||
        (inner.2.1 ≤ outer.2.1 && outer.2.2 ≤ inner.2.2)

/-- Every extracted span is nonempty, in bounds, and nested or disjoint with every other span. -/
example : tree.map (fun parsed ↦ spansWellFormed parsed sentence.size) = some true := by
  native_decide

/-- Re-scoring the production-identity-free tree recovers the canonical Viterbi goal. -/
example :
    (tree.bind (treeScore grammar)).map
      (fun score ↦ decide (Float.abs (score.toFloat - chartGoal.toFloat) < 1e-12)) = some true := by
  native_decide

private def ruleTieGrammar : CNF Vit :=
  { bin := #[⟨0, 3, 4, ⟨1.0⟩⟩, ⟨0, 1, 2, ⟨1.0⟩⟩]
    lex := #[⟨1, 10, ⟨1.0⟩⟩, ⟨3, 10, ⟨1.0⟩⟩,
      ⟨2, 11, ⟨1.0⟩⟩, ⟨4, 11, ⟨1.0⟩⟩]
    start := 0
    nNT := 5 }

private def ruleTieWords : Array Tok := #[10, 11]
private def ruleTieIndexed := ruleTieGrammar.index
private def ruleTieChart := Nlp.Parse.Viterbi.ckyVit ruleTieIndexed ruleTieWords
private def ruleTieTree :=
  Nlp.Parse.Viterbi.extractTree ruleTieIndexed ruleTieWords ruleTieChart

/-- Pair bucketing reverses these rules, but equal scores still choose source `CNF.bin[0]`. -/
example : ruleTieIndexed.binSource = #[1, 0] := by native_decide

example :
    (ruleTieChart.back.getD (goalIndex ruleTieGrammar ruleTieWords.size) default).rule = 0 := by
  native_decide

example :
    ruleTieTree.map (fun parsed ↦ parsed.spans.map (fun span ↦ span.1)) =
      some #[0, 3, 4] := by
  native_decide

private def splitTieGrammar : CNF Vit :=
  { bin :=
      #[ ⟨0, 1, 4, ⟨1.0⟩⟩,
         ⟨0, 5, 3, ⟨1.0⟩⟩,
         ⟨4, 2, 3, ⟨1.0⟩⟩,
         ⟨5, 1, 2, ⟨1.0⟩⟩ ]
    lex := #[⟨1, 20, ⟨1.0⟩⟩, ⟨2, 21, ⟨1.0⟩⟩, ⟨3, 22, ⟨1.0⟩⟩]
    start := 0
    nNT := 6 }

private def splitTieWords : Array Tok := #[20, 21, 22]
private def splitTieIndexed := splitTieGrammar.index
private def splitTieChart := Nlp.Parse.Viterbi.ckyVit splitTieIndexed splitTieWords

/-- Equal derivations at different splits choose the leftmost split. -/
example :
    (splitTieChart.back.getD (goalIndex splitTieGrammar splitTieWords.size) default).split = 1 := by
  native_decide

private def malformedBaseGrammar : CNF Vit :=
  { bin := #[⟨0, 1, 2, ⟨1.0⟩⟩]
    lex := #[⟨1, 40, ⟨1.0⟩⟩, ⟨2, 41, ⟨1.0⟩⟩]
    start := 0
    nNT := 3 }

private def malformedWords : Array Tok := #[40, 41]
private def wellIndexed := malformedBaseGrammar.index

private def truncatedIndex : IndexedCNF Vit :=
  { wellIndexed with pairStart := #[] }

private def overrunIndex : IndexedCNF Vit :=
  let stop := IndexedCNF.pairKey malformedBaseGrammar.nNT 1 2 + 1
  { wellIndexed with
    binSource := #[malformedBaseGrammar.bin.size]
    pairStart := wellIndexed.pairStart.set! stop (wellIndexed.binSorted.size + 100) }

private def outOfBoundsRule : BinRule Vit := ⟨99, 1, 2, ⟨1.0⟩⟩

private def invalidRuleGrammar : CNF Vit :=
  { malformedBaseGrammar with bin := malformedBaseGrammar.bin.push outOfBoundsRule }

private def invalidRuleIndex : IndexedCNF Vit :=
  let pairStart := malformedBaseGrammar.index.pairStart
  { grammar := invalidRuleGrammar
    binSorted := #[outOfBoundsRule]
    binSource := #[1]
    pairStart }

private def malformedGoal (index : IndexedCNF Vit) : Float :=
  let malformedChart := Nlp.Parse.Viterbi.ckyVit index malformedWords
  malformedChart.score.getD (goalIndex index.grammar malformedWords.size) 0 |>.toFloat

/-- Truncated, overrun, and invalid-rule indexes are conservative and execute without OOB reads. -/
example : malformedGoal truncatedIndex == 0.0 := by native_decide
example : malformedGoal overrunIndex == 0.0 := by native_decide
example : malformedGoal invalidRuleIndex == 0.0 := by native_decide

private def duplicateGrammar : CNF Vit :=
  { bin := #[⟨0, 1, 2, ⟨0.4⟩⟩, ⟨0, 1, 2, ⟨0.8⟩⟩]
    lex := #[⟨1, 50, ⟨0.5⟩⟩, ⟨1, 50, ⟨0.9⟩⟩, ⟨2, 51, ⟨1.0⟩⟩]
    start := 0
    nNT := 3 }

private def duplicateWords : Array Tok := #[50, 51]
private def duplicateIndexed := duplicateGrammar.index
private def duplicateChart := Nlp.Parse.Viterbi.ckyVit duplicateIndexed duplicateWords
private def duplicateGoal : Vit :=
  duplicateChart.score.getD (goalIndex duplicateGrammar duplicateWords.size) 0
private def duplicateTree :=
  Nlp.Parse.Viterbi.extractTree duplicateIndexed duplicateWords duplicateChart

/-- Re-scoring sums erased duplicate identities, so the extracted tree attains the chart goal. -/
example :
    (duplicateTree.bind (treeScore duplicateGrammar)).map
      (fun score ↦ decide (Float.abs (score.toFloat - duplicateGoal.toFloat) < 1e-12)) =
        some true := by
  native_decide

example : Float.abs (duplicateGoal.toFloat - 0.72) < 1e-12 := by native_decide

private def rejectedWords : Array Tok := #[99]

example :
    (Nlp.Parse.Viterbi.extractTree indexed rejectedWords
      (Nlp.Parse.Viterbi.ckyVit indexed rejectedWords)).isNone = true := by
  native_decide

example :
    (Nlp.Parse.Viterbi.extractTree indexed #[]
      (Nlp.Parse.Viterbi.ckyVit indexed #[])).isNone = true := by
  native_decide

private def malformedBack : Nlp.Parse.Viterbi.VitChart :=
  { chart with
    back := chart.back.set! (goalIndex grammar sentence.size) ⟨0, 0⟩ }

example : (Nlp.Parse.Viterbi.extractTree indexed sentence malformedBack).isNone = true := by
  native_decide

private def malformedSize : Nlp.Parse.Viterbi.VitChart := ⟨#[], #[]⟩

example : (Nlp.Parse.Viterbi.extractTree indexed sentence malformedSize).isNone = true := by
  native_decide

end NlpTests.Parse.Viterbi
