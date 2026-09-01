/-!
# Named constituency trees

`NamedTree` is the presentation-side constituency shape: leaves retain surface forms and phrasal
nodes retain category names. Every phrasal node has a distinguished first child, so empty phrases
are unrepresentable.
-/

namespace Nlp

/-- An n-ary named constituency tree with at least one child at every phrasal node. -/
inductive NamedTree where
  | leaf (form : String)
  | node (category : String) (child : NamedTree) (children : Array NamedTree)
deriving Repr, Inhabited, BEq

namespace NamedTree

/-- Fold a named tree. Recursion through array children remains structurally total. -/
def cata (onLeaf : String → α) (onNode : String → α → Array α → α) : NamedTree → α
  | .leaf form => onLeaf form
  | .node category child children =>
      onNode category (cata onLeaf onNode child)
        (children.attach.map fun ⟨tree, _⟩ ↦ cata onLeaf onNode tree)

/-- Number of terminal forms in a named tree. -/
def width : NamedTree → Nat
  | .leaf _ => 1
  | .node _ child children =>
      children.attach.foldl (fun total ⟨tree, _⟩ ↦ total + tree.width) child.width

/-- Append the terminal yield to an existing output buffer in left-to-right order. -/
def yieldFormsInto : NamedTree → Array String → Array String
  | .leaf form, output => output.push form
  | .node _ child children, output =>
      children.attach.foldl
        (fun forms ⟨tree, _⟩ ↦ tree.yieldFormsInto forms)
        (child.yieldFormsInto output)

/-- Terminal forms in left-to-right order. -/
def yieldForms (tree : NamedTree) : Array String :=
  tree.yieldFormsInto #[]

/-- Append preorder named phrasal spans to a buffer and return the final fencepost. -/
def spansInto : NamedTree → Nat → Array (String × Nat × Nat) →
    Array (String × Nat × Nat) × Nat
  | .leaf _, start, output => (output, start + 1)
  | .node category child children, start, output =>
      let rootIndex := output.size
      let output := output.push (category, start, start)
      let (output, afterFirst) := child.spansInto start output
      let (output, stop) := children.attach.foldl
        (fun (accumulator, offset) ⟨tree, _⟩ ↦ tree.spansInto offset accumulator)
        (output, afterFirst)
      (output.set! rootIndex (category, start, stop), stop)

/-- Named phrasal spans and the final fencepost from a caller-selected start. -/
def spansFrom (tree : NamedTree) (start : Nat) :
    Array (String × Nat × Nat) × Nat :=
  tree.spansInto start #[]

/-- Preorder phrasal spans as `(category, start, stop)` fencepost triples. -/
def spans (tree : NamedTree) (start : Nat := 0) : Array (String × Nat × Nat) :=
  (tree.spansFrom start).1

/-- Check recursively that every phrasal category is nonempty. -/
def categoriesNonempty : NamedTree → Bool
  | .leaf _ => true
  | .node category child children =>
      !category.isEmpty && child.categoriesNonempty &&
        children.attach.all fun ⟨tree, _⟩ ↦ tree.categoriesNonempty

/-- Induction over named trees with a pointwise hypothesis for the array children. -/
theorem inductionOn {motive : NamedTree → Prop} (tree : NamedTree)
    (leaf : ∀ form, motive (.leaf form))
    (node : ∀ category child children, motive child →
      (∀ next ∈ children, motive next) → motive (.node category child children)) :
    motive tree :=
  match tree with
  | .leaf form => leaf form
  | .node category child children =>
      node category child children (inductionOn child leaf node)
        fun next _ ↦ inductionOn next leaf node
termination_by tree

private theorem foldl_yieldFormsInto_prefix :
    ∀ trees : List NamedTree,
      (∀ tree ∈ trees, ∀ output : Array String,
        tree.yieldFormsInto output = output ++ tree.yieldForms) →
      ∀ pre initial : Array String,
        trees.foldl (fun output tree ↦ tree.yieldFormsInto output) (pre ++ initial) =
          pre ++ trees.foldl (fun output tree ↦ tree.yieldFormsInto output) initial
  | [], _, _, _ => rfl
  | tree :: trees, hypothesis, pre, initial => by
      simp only [List.foldl_cons]
      rw [hypothesis tree (by simp) (pre ++ initial), Array.append_assoc]
      rw [foldl_yieldFormsInto_prefix trees
        (fun next member ↦ hypothesis next (by simp [member])) pre
        (initial ++ tree.yieldForms)]
      rw [hypothesis tree (by simp) initial]

/-- Appending a yield preserves the buffer and appends the standalone terminal yield. -/
theorem yieldFormsInto_eq_append (tree : NamedTree) : ∀ output : Array String,
    tree.yieldFormsInto output = output ++ tree.yieldForms := by
  induction tree using inductionOn with
  | leaf form => intro output; simp [yieldForms, yieldFormsInto]
  | node category child children childIH childrenIH =>
      intro output
      simp only [yieldForms, yieldFormsInto]
      rw [Array.foldl_attach
        (f := fun forms (next : NamedTree) ↦ next.yieldFormsInto forms)]
      rw [Array.foldl_attach
        (f := fun forms (next : NamedTree) ↦ next.yieldFormsInto forms)]
      simp only [childIH, Array.empty_append]
      rw [← Array.foldl_toList, ← Array.foldl_toList]
      exact foldl_yieldFormsInto_prefix children.toList
        (fun next member ↦ childrenIH next (by simpa using member)) output child.yieldForms

/-- A leaf covers exactly one terminal. -/
@[simp] theorem width_leaf (form : String) : (NamedTree.leaf form).width = 1 := by
  simp [width]

/-- Width at a phrasal node is a plain fold over its remaining children. -/
theorem width_node (category : String) (child : NamedTree) (children : Array NamedTree) :
    (NamedTree.node category child children).width =
      children.foldl (fun total tree ↦ total + tree.width) child.width := by
  simp [width]

/-- The terminal yield of a leaf is its singleton form. -/
@[simp] theorem yieldForms_leaf (form : String) :
    (NamedTree.leaf form).yieldForms = #[form] := by
  simp [yieldForms, yieldFormsInto]

/-- The terminal yield of a phrasal node is the concatenation of its child yields. -/
theorem yieldForms_node (category : String) (child : NamedTree)
    (children : Array NamedTree) :
    (NamedTree.node category child children).yieldForms =
      children.foldl (fun forms tree ↦ forms ++ tree.yieldForms) child.yieldForms := by
  change (NamedTree.node category child children).yieldFormsInto #[] = _
  rw [yieldFormsInto]
  change children.attach.foldl
      (fun forms tree ↦ tree.1.yieldFormsInto forms) (child.yieldFormsInto #[]) = _
  rw [Array.foldl_attach
    (f := fun forms (tree : NamedTree) ↦ tree.yieldFormsInto forms)]
  simp only [yieldFormsInto_eq_append, Array.empty_append]

private theorem le_foldl_width :
    ∀ trees : List NamedTree, ∀ initial : Nat,
      initial ≤ trees.foldl (fun total tree ↦ total + tree.width) initial
  | [], initial => Nat.le_refl initial
  | tree :: trees, initial =>
      Nat.le_trans (Nat.le_add_right initial tree.width)
        (le_foldl_width trees (initial + tree.width))

/-- Every named tree covers at least one terminal form. -/
theorem width_pos : ∀ tree : NamedTree, 0 < tree.width
  | .leaf _ => by simp
  | .node _ child children => by
      rw [width_node, ← Array.foldl_toList]
      exact Nat.lt_of_lt_of_le (width_pos child)
        (le_foldl_width children.toList child.width)

private theorem size_foldl_append :
    ∀ trees : List NamedTree,
      (∀ tree ∈ trees, tree.yieldForms.size = tree.width) →
      ∀ forms : Array String,
        (trees.foldl (fun output tree ↦ output ++ tree.yieldForms) forms).size =
          trees.foldl (fun total tree ↦ total + tree.width) forms.size
  | [], _, _ => rfl
  | tree :: trees, hypothesis, forms => by
      simp only [List.foldl_cons]
      rw [size_foldl_append trees
          (fun next member ↦ hypothesis next (by simp [member]))
          (forms ++ tree.yieldForms),
        Array.size_append, hypothesis tree (by simp)]

/-- The terminal yield contains exactly `width` forms. -/
theorem yieldForms_size (tree : NamedTree) : tree.yieldForms.size = tree.width := by
  induction tree using inductionOn with
  | leaf form => simp
  | node category child children childIH childrenIH =>
      rw [yieldForms_node, width_node, ← Array.foldl_toList, ← Array.foldl_toList, ← childIH]
      exact size_foldl_append children.toList
        (fun next member ↦ childrenIH next (by simpa using member)) child.yieldForms

/-- Appending a tree yield increases a buffer's size by exactly the tree width. -/
theorem yieldFormsInto_size (tree : NamedTree) (output : Array String) :
    (tree.yieldFormsInto output).size = output.size + tree.width := by
  rw [yieldFormsInto_eq_append, Array.size_append, yieldForms_size]

end NamedTree
end Nlp
