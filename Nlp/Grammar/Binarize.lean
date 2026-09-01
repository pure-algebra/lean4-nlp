import Nlp.Syntax.Tree

/-!
# Lossless constituency-tree binarization

Synthetic right-spine nodes are represented by their own constructor.  Real categories therefore
cannot be mistaken for implementation nodes, and debinarization is total.  The transformation is
pure: callers may retain either the original n-ary tree or its binary view without runtime state.
-/

namespace Nlp.Grammar

/-- A constituency tree whose synthetic right spine is explicit in the type. -/
inductive BTree where
  | leaf (word : Word)
  | unary (cat : Cat) (child : BTree)
  | bin (cat : Cat) (left right : BTree)
  | syn (cat : Cat) (left right : BTree)
deriving Repr, Inhabited, DecidableEq

namespace BTree

/-- Build the lossless right-branching tail headed by `first`. -/
def spine (cat : Cat) : BTree → List BTree → BTree
  | first, [] => first
  | first, next :: rest => .syn cat first (spine cat next rest)

mutual
  /-- Recover one real tree from a binary tree.  A synthetic root is treated as an ordinary node. -/
  def debinarize : BTree → Tree
    | .leaf word => .leaf word
    | .unary cat child => .node cat child.debinarize #[]
    | .bin cat left right => .node cat left.debinarize right.kids.toArray
    | .syn cat left right => .node cat left.debinarize right.kids.toArray

  /-- Flatten a binary subtree when it occurs in the right-child position of a real node. -/
  def kids : BTree → List Tree
    | .leaf word => [.leaf word]
    | .unary cat child => [.node cat child.debinarize #[]]
    | .bin cat left right => [.node cat left.debinarize right.kids.toArray]
    | .syn _ left right => left.debinarize :: right.kids
end

/-- Whether a binary tree has a real rather than synthetic root. -/
def RealRoot : BTree → Prop
  | .syn _ _ _ => False
  | _ => True

theorem kids_eq_singleton {tree : BTree} (real : tree.RealRoot) :
    tree.kids = [tree.debinarize] := by
  cases tree <;> simp_all [RealRoot, kids, debinarize]

/-- Append the terminal yield to an existing buffer, ignoring synthetic nodes. -/
def yieldWordsInto : BTree → Array Word → Array Word
  | .leaf word, output => output.push word
  | .unary _ child, output => child.yieldWordsInto output
  | .bin _ left right, output => right.yieldWordsInto (left.yieldWordsInto output)
  | .syn _ left right, output => right.yieldWordsInto (left.yieldWordsInto output)

/-- The terminal yield of a binary tree in left-to-right order. -/
def yieldWords (tree : BTree) : Array Word :=
  tree.yieldWordsInto #[]

end BTree

mutual
  /-- Losslessly convert an n-ary constituency tree to a right-branching binary tree. -/
  def binarize : Tree → BTree
    | .leaf word => .leaf word
    | .node cat child ⟨[]⟩ => .unary cat (binarize child)
    | .node cat child ⟨next :: rest⟩ =>
        .bin cat (binarize child) (binarizeSpine cat next rest)
  termination_by tree => sizeOf tree
  decreasing_by
    all_goals simp_wf <;> omega

  /-- Build a right spine directly from the remaining original children. -/
  private def binarizeSpine (cat : Cat) (first : Tree) : List Tree → BTree
    | [] => binarize first
    | next :: rest => .syn cat (binarize first) (binarizeSpine cat next rest)
  termination_by rest => sizeOf first + sizeOf rest
  decreasing_by
    all_goals simp_wf <;> omega
end

/-- Total inverse view from binary trees to ordinary n-ary constituency trees. -/
abbrev debinarize := BTree.debinarize

/-- Binarization never exposes a synthetic node at the root. -/
theorem binarize_realRoot (tree : Tree) : (binarize tree).RealRoot := by
  cases tree with
  | leaf => simp [binarize, BTree.RealRoot]
  | node _ _ children =>
      cases children with
      | mk children => cases children <;> simp [binarize, BTree.RealRoot]

mutual
  /-- Lossless binarization followed by debinarization returns the original tree. -/
  theorem debinarize_binarize (tree : Tree) : (binarize tree).debinarize = tree := by
    cases tree with
    | leaf => simp [binarize, BTree.debinarize]
    | node cat child children =>
        cases children with
        | mk children =>
            cases children with
            | nil =>
                simp only [binarize, BTree.debinarize]
                have childInverse := debinarize_binarize child
                rw [childInverse]
            | cons next rest =>
                simp only [binarize, BTree.debinarize]
                have childInverse := debinarize_binarize child
                have childrenInverse := kids_binarizeSpine cat next rest
                rw [childInverse, childrenInverse]
  termination_by sizeOf tree
  decreasing_by
    all_goals simp_wf <;> omega

  private theorem kids_binarizeSpine (cat : Cat) (first : Tree) (rest : List Tree) :
      (binarizeSpine cat first rest).kids = first :: rest := by
    cases rest with
    | nil =>
        calc
          (binarizeSpine cat first []).kids = (binarize first).kids := by
            simp [binarizeSpine]
          _ = [(binarize first).debinarize] :=
            BTree.kids_eq_singleton (binarize_realRoot first)
          _ = [first] := congrArg (fun tree ↦ [tree]) (debinarize_binarize first)
    | cons next rest =>
        simp only [binarizeSpine, BTree.kids]
        have firstInverse := debinarize_binarize first
        have restInverse := kids_binarizeSpine cat next rest
        rw [firstInverse, restInverse]
  termination_by sizeOf first + sizeOf rest
  decreasing_by
    all_goals simp_wf <;> omega
end

mutual
  theorem binarize_yieldWordsInto (tree : Tree) (output : Array Word) :
      (binarize tree).yieldWordsInto output = tree.yieldWordsInto output := by
    cases tree with
    | leaf => simp [binarize, BTree.yieldWordsInto, Tree.yieldWordsInto]
    | node cat child children =>
        cases children with
        | mk children =>
            cases children with
            | nil =>
                simp only [binarize, BTree.yieldWordsInto, Tree.yieldWordsInto]
                rw [binarize_yieldWordsInto child output]
                rw [Array.foldl_attach
                  (f := fun words (tree : Tree) ↦ tree.yieldWordsInto words)]
                rw [← Array.foldl_toList]
                rfl
            | cons next rest =>
                simp only [binarize, BTree.yieldWordsInto, Tree.yieldWordsInto]
                rw [binarize_yieldWordsInto child output]
                rw [yieldWordsInto_binarizeSpine cat next rest]
                rw [Array.foldl_attach
                  (f := fun words (tree : Tree) ↦ tree.yieldWordsInto words)]
                rw [← Array.foldl_toList]
                rfl
  termination_by sizeOf tree
  decreasing_by
    all_goals simp_wf <;> omega

  private theorem yieldWordsInto_binarizeSpine (cat : Cat) (first : Tree)
      (rest : List Tree) (output : Array Word) :
      (binarizeSpine cat first rest).yieldWordsInto output =
        rest.foldl (fun words tree ↦ tree.yieldWordsInto words)
          (first.yieldWordsInto output) := by
    cases rest with
    | nil =>
        simp only [binarizeSpine, List.foldl_nil]
        exact binarize_yieldWordsInto first output
    | cons next rest =>
        simp only [binarizeSpine, BTree.yieldWordsInto, List.foldl_cons]
        rw [binarize_yieldWordsInto first output]
        exact yieldWordsInto_binarizeSpine cat next rest (first.yieldWordsInto output)
  termination_by sizeOf first + sizeOf rest
  decreasing_by
    all_goals simp_wf <;> omega
end

/-- Binarization preserves the terminal yield without allocating an intermediate ordinary tree. -/
theorem binarize_yieldWords (tree : Tree) :
    (binarize tree).yieldWords = tree.yieldWords := by
  exact binarize_yieldWordsInto tree #[]

end Nlp.Grammar
