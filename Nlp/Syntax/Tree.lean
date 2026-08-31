/-!
# Constituency trees

The stored representation uses interned identifiers and array-backed children. A phrasal node
has a distinguished first child, so an empty phrasal node is unrepresentable.
-/

namespace Nlp

/-- An interned nonterminal or preterminal identifier. -/
abbrev Cat := UInt32

/-- An interned surface-word identifier. -/
abbrev Word := UInt32

/-- An n-ary constituency tree with at least one child at every phrasal node. -/
inductive Tree where
  | leaf (word : Word)
  | node (cat : Cat) (child : Tree) (children : Array Tree)
deriving Repr, Inhabited

namespace Tree

/-- Fold a tree. Recursion through array children uses `Array.attach` so it remains total. -/
def cata (onLeaf : Word → α) (onNode : Cat → α → Array α → α) : Tree → α
  | .leaf word => onLeaf word
  | .node cat child children =>
      onNode cat (cata onLeaf onNode child)
        (children.attach.map fun ⟨tree, _⟩ => cata onLeaf onNode tree)

/-- Fold a tree while retaining each original subtree alongside its folded result. -/
def para (onLeaf : Word → α)
    (onNode : Cat → Tree × α → Array (Tree × α) → α) : Tree → α
  | .leaf word => onLeaf word
  | .node cat child children =>
      onNode cat (child, para onLeaf onNode child)
        (children.attach.map fun ⟨tree, _⟩ => (tree, para onLeaf onNode tree))

/-- Number of terminal leaves in the tree. -/
def width : Tree → Nat
  | .leaf _ => 1
  | .node _ child children =>
      children.attach.foldl (fun total ⟨tree, _⟩ => total + tree.width) child.width

/-- Terminal yield in left-to-right order. -/
def yieldWords (tree : Tree) : Array Word :=
  tree.cata (fun word => #[word]) fun _ first rest =>
    rest.foldl (fun words childWords => words ++ childWords) first

/-- Preorder phrasal-node spans as `(category, start, stop)` fencepost triples. -/
def spansFrom : Tree → Nat → Array (Cat × Nat × Nat) × Nat
  | .leaf _, start => (#[], start + 1)
  | .node cat child children, start =>
      let (firstSpans, afterFirst) := spansFrom child start
      let (childSpans, stop) := children.attach.foldl
        (fun (acc, offset) ⟨tree, _⟩ =>
          let (next, afterTree) := spansFrom tree offset
          (acc ++ next, afterTree))
        (firstSpans, afterFirst)
      (#[(cat, start, stop)] ++ childSpans, stop)

/-- Compute all phrasal-node spans in one traversal, starting at fencepost `start`. -/
def spans (tree : Tree) (start : Nat := 0) : Array (Cat × Nat × Nat) :=
  (tree.spansFrom start).1

end Tree
end Nlp
