import Nlp.Syntax.Tree

namespace NlpTests.Syntax.Tree

open Nlp

private def sample : Tree :=
  .node 0 (.leaf 10) #[.node 1 (.leaf 11) #[.leaf 12], .leaf 13]

private def flat : Tree :=
  .node 5 (.leaf 20)
    #[.leaf 21, .leaf 22, .leaf 23, .leaf 24, .leaf 25, .leaf 26, .leaf 27]

private def skew : Tree :=
  .node 0
    (.node 1
      (.node 2
        (.node 3 (.node 4 (.leaf 30) #[]) #[]) #[]) #[]) #[]

private def yieldWordsReference (tree : Tree) : Array Word :=
  tree.cata (fun word ↦ #[word]) fun _ first rest ↦
    rest.foldl (fun words childWords ↦ words ++ childWords) first

private def spansFromReference : Tree → Nat → Array (Cat × Nat × Nat) × Nat
  | .leaf _, start => (#[], start + 1)
  | .node cat child children, start =>
      let (firstSpans, afterFirst) := spansFromReference child start
      let (childSpans, stop) := children.attach.foldl
        (fun (accumulator, offset) ⟨tree, _⟩ ↦
          let (next, afterTree) := spansFromReference tree offset
          (accumulator ++ next, afterTree))
        (firstSpans, afterFirst)
      (#[(cat, start, stop)] ++ childSpans, stop)

private def smallTrees : Nat → Array Tree
  | 0 => #[.leaf 0, .leaf 1]
  | depth + 1 => Id.run do
      let smaller := smallTrees depth
      let mut output := smaller
      for cat in #[0, 1] do
        for first in smaller do
          output := output.push (.node cat first #[])
          for second in smaller do
            output := output.push (.node cat first #[second])
      return output

#guard sample.width == 4

#guard sample.yieldWords == #[10, 11, 12, 13]

#guard sample.spans == #[(0, 0, 4), (1, 1, 3)]

#guard flat.yieldWords == #[20, 21, 22, 23, 24, 25, 26, 27]

#guard flat.spans 7 == #[(5, 7, 15)]

#guard skew.yieldWords == #[30]

#guard skew.spans 2 ==
  #[(0, 2, 3), (1, 2, 3), (2, 2, 3), (3, 2, 3), (4, 2, 3)]

-- The accumulator implementations agree with the former concatenating definitions.
#guard (smallTrees 2).all fun tree ↦
  tree.yieldWords == yieldWordsReference tree &&
    tree.spansFrom 3 == spansFromReference tree 3

#guard (smallTrees 2).all fun tree ↦
  tree.yieldWordsInto #[90, 91] == #[90, 91] ++ yieldWordsReference tree &&
    tree.spansInto 3 #[(9, 1, 2)] ==
      (#[(9, 1, 2)] ++ (spansFromReference tree 3).1, (spansFromReference tree 3).2)

#guard sample.cata (fun _ => 1) (fun _ first rest => 1 + first + rest.foldl (· + ·) 0) == 6

end NlpTests.Syntax.Tree
