import Nlp.Grammar.Binarize

namespace NlpTests.Grammar.Binarize

open Nlp Nlp.Grammar

private def unary : Tree :=
  .node 10 (.leaf 1) #[]

private def binary : Tree :=
  .node 20 (.leaf 1) #[.leaf 2]

private def ternary : Tree :=
  .node 30 (.leaf 1) #[.leaf 2, .leaf 3]

private def nested : Tree :=
  .node 40
    (.node 41 (.leaf 1) #[.leaf 2, .leaf 3])
    #[.node 42 (.leaf 4) #[], .leaf 5, .leaf 6]

example : binarize unary = .unary 10 (.leaf 1) := by
  native_decide

example : binarize binary = .bin 20 (.leaf 1) (.leaf 2) := by
  native_decide

example : binarize ternary =
    .bin 30 (.leaf 1) (.syn 30 (.leaf 2) (.leaf 3)) := by
  native_decide

example : (binarize nested).yieldWords = #[1, 2, 3, 4, 5, 6] := by
  native_decide

example : (binarize nested).debinarize = nested :=
  debinarize_binarize nested

example : (binarize nested).yieldWords = nested.yieldWords :=
  binarize_yieldWords nested

example : (binarize nested).RealRoot :=
  binarize_realRoot nested

example : (binarize nested).kids = [(binarize nested).debinarize] :=
  BTree.kids_eq_singleton (binarize_realRoot nested)

private def syntheticRoot : BTree :=
  .syn 99 (.leaf 7) (.syn 99 (.leaf 8) (.leaf 9))

example : syntheticRoot.yieldWords = #[7, 8, 9] := by
  native_decide

example : syntheticRoot.debinarize.yieldWords = #[7, 8, 9] := by
  native_decide

example : ¬syntheticRoot.RealRoot := by
  simp [syntheticRoot, BTree.RealRoot]

end NlpTests.Grammar.Binarize
