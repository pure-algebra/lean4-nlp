import Nlp.Syntax.Tree

/-!
# Coherence lemmas for constituency trees

Structural facts tying together the `Tree` traversals defined in `Nlp.Syntax.Tree`:

* `Tree.inductionOn`: induction with a membership hypothesis for the array-backed children,
  usable where the auto-generated recursor for the nested inductive is awkward.
* `Tree.width_pos`: every tree covers at least one terminal.
* `Tree.yieldWords_size`: the terminal yield has exactly `width` words.
* `Tree.spansFrom_snd`: parsing forward from fencepost `start` ends at `start + width`.
* `Tree.spansFrom_mem_bounds` / `Tree.spans_mem_bounds`: every recorded span is nonempty and
  lies inside the tree's own fencepost interval.

The unfold lemmas (`width_node`, `yieldWords_node`, `spansFrom_node_fst`, `spansFrom_node_snd`)
restate the `Array.attach`-based definitions as plain `Array.foldl` folds, which is the form the
proofs — and downstream users — actually want to compute with.
-/

namespace Nlp
namespace Tree

/-- Induction over `Tree` with a pointwise hypothesis for the array children.

The nested `Array Tree` field means plain `induction` does not give a usable hypothesis for the
children; this principle provides the membership-based one. -/
theorem inductionOn {motive : Tree → Prop} (t : Tree)
    (leaf : ∀ w, motive (.leaf w))
    (node : ∀ c child children, motive child → (∀ x ∈ children, motive x) →
      motive (.node c child children)) : motive t :=
  match t with
  | .leaf w => leaf w
  | .node c child children =>
      node c child children (inductionOn child leaf node)
        fun x _ => inductionOn x leaf node
termination_by t

/-! ## Unfold lemmas -/

private theorem foldl_yieldWordsInto_prefix :
    ∀ (trees : List Tree),
      (∀ tree ∈ trees, ∀ output : Array Word,
        tree.yieldWordsInto output = output ++ tree.yieldWords) →
      ∀ pre initial : Array Word,
        trees.foldl (fun output tree ↦ tree.yieldWordsInto output) (pre ++ initial) =
          pre ++ trees.foldl (fun output tree ↦ tree.yieldWordsInto output) initial
  | [], _, _, _ => rfl
  | tree :: trees, hypothesis, pre, initial => by
      simp only [List.foldl_cons]
      rw [hypothesis tree (by simp) (pre ++ initial), Array.append_assoc]
      rw [foldl_yieldWordsInto_prefix trees
        (fun next member ↦ hypothesis next (by simp [member])) pre
        (initial ++ tree.yieldWords)]
      rw [hypothesis tree (by simp) initial]

/-- Appending a tree yield into a buffer is equivalent to appending the standalone yield. -/
theorem yieldWordsInto_eq_append (t : Tree) : ∀ output : Array Word,
    t.yieldWordsInto output = output ++ t.yieldWords := by
  induction t using inductionOn with
  | leaf word => intro output; simp [yieldWords, yieldWordsInto]
  | node cat child children childIH childrenIH =>
      intro output
      simp only [yieldWords, yieldWordsInto]
      rw [Array.foldl_attach
        (f := fun words (tree : Tree) ↦ tree.yieldWordsInto words)]
      rw [Array.foldl_attach
        (f := fun words (tree : Tree) ↦ tree.yieldWordsInto words)]
      simp only [childIH, Array.empty_append]
      rw [← Array.foldl_toList, ← Array.foldl_toList]
      exact foldl_yieldWordsInto_prefix children.toList
        (fun tree member ↦ childrenIH tree (by simpa using member)) output child.yieldWords

/-- One step of the `spansFrom` child fold: parse the next child at the current fencepost. -/
abbrev spanStep (acc : Array (Cat × Nat × Nat) × Nat) (t : Tree) :
    Array (Cat × Nat × Nat) × Nat :=
  (acc.1 ++ (t.spansFrom acc.2).1, (t.spansFrom acc.2).2)

private abbrev spansIntoStep
    (state : Array (Cat × Nat × Nat) × Nat) (tree : Tree) :
    Array (Cat × Nat × Nat) × Nat :=
  tree.spansInto state.2 state.1

private theorem foldl_spansInto_prefix :
    ∀ (trees : List Tree),
      (∀ tree ∈ trees, ∀ start output,
        tree.spansInto start output =
          (output ++ (tree.spansFrom start).1, (tree.spansFrom start).2)) →
      ∀ pre state,
        trees.foldl spansIntoStep (pre ++ state.1, state.2) =
          let result := trees.foldl spansIntoStep state
          (pre ++ result.1, result.2)
  | [], _, _, _ => rfl
  | tree :: trees, hypothesis, pre, state => by
      simp only [List.foldl_cons, spansIntoStep]
      rw [hypothesis tree (by simp) state.2 (pre ++ state.1)]
      rw [hypothesis tree (by simp) state.2 state.1]
      rw [Array.append_assoc]
      exact foldl_spansInto_prefix trees
        (fun next member ↦ hypothesis next (by simp [member])) pre
        (state.1 ++ (tree.spansFrom state.2).1, (tree.spansFrom state.2).2)

private theorem arrayFoldl_spansInto_prefix (trees : Array Tree)
    (hypothesis : ∀ tree ∈ trees, ∀ start output,
      tree.spansInto start output =
        (output ++ (tree.spansFrom start).1, (tree.spansFrom start).2))
    (pre : Array (Cat × Nat × Nat))
    (state : Array (Cat × Nat × Nat) × Nat) :
    trees.foldl spansIntoStep (pre ++ state.1, state.2) =
      let result := trees.foldl spansIntoStep state
      (pre ++ result.1, result.2) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_spansInto_prefix trees.toList
    (fun tree member ↦ hypothesis tree (by simpa using member)) pre state

/-- Appending spans into a buffer preserves the buffer and the standalone traversal result. -/
theorem spansInto_eq_append (tree : Tree) : ∀ start output,
    tree.spansInto start output =
      (output ++ (tree.spansFrom start).1, (tree.spansFrom start).2) := by
  induction tree using inductionOn with
  | leaf word => intro start output; simp [spansFrom, spansInto]
  | node cat child children childIH childrenIH =>
      intro start output
      simp only [spansFrom, spansInto]
      simp only [childIH]
      repeat rw [Array.foldl_attach (f := spansIntoStep)]
      rw [← Array.append_singleton_assoc]
      rw [arrayFoldl_spansInto_prefix children
        (fun tree member ↦ childrenIH tree member) output
        (#[(cat, start, start)] ++ (child.spansFrom start).1,
          (child.spansFrom start).2)]
      simp [Array.setIfInBounds_append_right]

private theorem spansIntoStep_eq_spanStep : spansIntoStep = spanStep := by
  funext state tree
  exact spansInto_eq_append tree state.2 state.1

private theorem arrayFoldl_spanStep_prefix (trees : Array Tree)
    (pre : Array (Cat × Nat × Nat))
    (state : Array (Cat × Nat × Nat) × Nat) :
    trees.foldl spanStep (pre ++ state.1, state.2) =
      let result := trees.foldl spanStep state
      (pre ++ result.1, result.2) := by
  have result := arrayFoldl_spansInto_prefix trees
    (fun tree _ ↦ spansInto_eq_append tree) pre state
  simpa only [spansIntoStep_eq_spanStep] using result

theorem width_leaf (w : Word) : (Tree.leaf w).width = 1 := by
  simp [width]

/-- `width` at a phrasal node is a plain fold over the children array. -/
theorem width_node (c : Cat) (child : Tree) (children : Array Tree) :
    (Tree.node c child children).width
      = children.foldl (fun total t ↦ total + t.width) child.width := by
  simp [width]

theorem yieldWords_leaf (w : Word) : (Tree.leaf w).yieldWords = #[w] := by
  simp [yieldWords, yieldWordsInto]

/-- `yieldWords` at a phrasal node is a plain fold over the children array. -/
theorem yieldWords_node (c : Cat) (child : Tree) (children : Array Tree) :
    (Tree.node c child children).yieldWords
      = children.foldl (fun words t ↦ words ++ t.yieldWords) child.yieldWords := by
  change (Tree.node c child children).yieldWordsInto #[] = _
  rw [yieldWordsInto]
  change children.attach.foldl
      (fun words tree ↦ tree.1.yieldWordsInto words) (child.yieldWordsInto #[]) = _
  rw [Array.foldl_attach
    (f := fun words (tree : Tree) ↦ tree.yieldWordsInto words)]
  simp only [yieldWordsInto_eq_append, Array.empty_append]

private theorem spansFrom_node_eq (c : Cat) (child : Tree) (children : Array Tree)
    (start : Nat) :
    (Tree.node c child children).spansFrom start =
      let result := children.foldl spanStep (child.spansFrom start)
      (#[(c, start, result.2)] ++ result.1, result.2) := by
  change (Tree.node c child children).spansInto start #[] = _
  rw [spansInto]
  rw [spansInto_eq_append child]
  simp only
  rw [Array.foldl_attach (f := spansIntoStep)]
  rw [spansIntoStep_eq_spanStep]
  simp only [Array.push_empty, Array.size_empty]
  rw [arrayFoldl_spanStep_prefix children #[(c, start, start)]
    (child.spansFrom start)]
  simp

theorem spansFrom_leaf (w : Word) (start : Nat) :
    (Tree.leaf w).spansFrom start = (#[], start + 1) := by
  simp [spansFrom, spansInto]

/-- The spans of a phrasal node: its own span, then the child spans, via a plain fold. -/
theorem spansFrom_node_fst (c : Cat) (child : Tree) (children : Array Tree) (start : Nat) :
    ((Tree.node c child children).spansFrom start).1
      = #[(c, start, (children.foldl spanStep (child.spansFrom start)).2)]
          ++ (children.foldl spanStep (child.spansFrom start)).1 := by
  rw [spansFrom_node_eq]

/-- The final fencepost of a phrasal node is the final fencepost of the child fold. -/
theorem spansFrom_node_snd (c : Cat) (child : Tree) (children : Array Tree) (start : Nat) :
    ((Tree.node c child children).spansFrom start).2
      = (children.foldl spanStep (child.spansFrom start)).2 := by
  rw [spansFrom_node_eq]

theorem spans_eq_spansFrom_fst (t : Tree) (start : Nat) :
    t.spans start = (t.spansFrom start).1 := rfl

/-! ## Width is positive -/

private theorem le_foldl_width :
    ∀ (l : List Tree) (init : Nat), init ≤ l.foldl (fun total t ↦ total + t.width) init
  | [], init => Nat.le_refl init
  | x :: xs, init =>
      Nat.le_trans (Nat.le_add_right init x.width) (le_foldl_width xs (init + x.width))

/-- Every tree spans at least one terminal. -/
theorem width_pos : ∀ t : Tree, 0 < t.width
  | .leaf _ => by simp [width_leaf]
  | .node _ child children => by
      rw [width_node, ← Array.foldl_toList]
      exact Nat.lt_of_lt_of_le (width_pos child) (le_foldl_width children.toList child.width)

/-! ## The yield has `width` words -/

private theorem size_foldl_append :
    ∀ (l : List Tree), (∀ x ∈ l, x.yieldWords.size = x.width) → ∀ words : Array Word,
      (l.foldl (fun ws t ↦ ws ++ t.yieldWords) words).size
        = l.foldl (fun total t ↦ total + t.width) words.size
  | [], _, _ => rfl
  | x :: xs, ih, words => by
      simp only [List.foldl_cons]
      rw [size_foldl_append xs (fun y hy ↦ ih y (by simp [hy])) (words ++ x.yieldWords),
        Array.size_append, ih x (by simp)]

/-- The terminal yield of a tree has exactly `width` entries. -/
theorem yieldWords_size (t : Tree) : t.yieldWords.size = t.width := by
  induction t using inductionOn with
  | leaf w => simp [yieldWords_leaf, width_leaf]
  | node c child children ih ihs =>
      rw [yieldWords_node, width_node, ← Array.foldl_toList, ← Array.foldl_toList, ← ih]
      exact size_foldl_append children.toList (fun x hx ↦ ihs x (by simpa using hx))
        child.yieldWords

/-! ## `spansFrom` ends at `start + width` -/

private theorem foldl_width_shift :
    ∀ (l : List Tree) (n init : Nat),
      l.foldl (fun total t ↦ total + t.width) (n + init)
        = n + l.foldl (fun total t ↦ total + t.width) init
  | [], _, _ => rfl
  | x :: xs, n, init => by
      simp only [List.foldl_cons]
      rw [Nat.add_assoc]
      exact foldl_width_shift xs n (init + x.width)

private theorem spansFold_snd :
    ∀ (l : List Tree), (∀ x ∈ l, ∀ st, (x.spansFrom st).2 = st + x.width) →
      ∀ q : Array (Cat × Nat × Nat) × Nat,
        (l.foldl spanStep q).2 = l.foldl (fun total t ↦ total + t.width) q.2
  | [], _, _ => rfl
  | x :: xs, ih, q => by
      simp only [List.foldl_cons]
      rw [spansFold_snd xs (fun y hy st ↦ ih y (by simp [hy]) st) (spanStep q x)]
      show List.foldl _ (x.spansFrom q.2).2 xs = _
      rw [ih x (by simp) q.2]

/-- Parsing forward from fencepost `start` ends exactly at `start + width`. -/
theorem spansFrom_snd (t : Tree) : ∀ start : Nat, (t.spansFrom start).2 = start + t.width := by
  induction t using inductionOn with
  | leaf w => intro start; rw [spansFrom_leaf, width_leaf]
  | node c child children ih ihs =>
      intro start
      rw [spansFrom_node_snd, ← Array.foldl_toList,
        spansFold_snd children.toList (fun x hx st ↦ ihs x (by simpa using hx) st)
          (child.spansFrom start),
        ih start, foldl_width_shift, width_node, ← Array.foldl_toList]

/-! ## Span bounds -/

private theorem spansFold_mem :
    ∀ (l : List Tree),
      (∀ x ∈ l, ∀ st s, s ∈ (x.spansFrom st).1 →
        st ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ st + x.width) →
      ∀ (q : Array (Cat × Nat × Nat) × Nat) (lo : Nat), lo ≤ q.2 →
        (∀ s ∈ q.1, lo ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ q.2) →
        ∀ s ∈ (l.foldl spanStep q).1,
          lo ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ (l.foldl spanStep q).2
  | [], _, _q, _lo, _hlo, hq => hq
  | x :: xs, ih, q, lo, hlo, hq => by
      simp only [List.foldl_cons]
      refine spansFold_mem xs (fun y hy ↦ ih y (by simp [hy])) (spanStep q x) lo ?_ ?_
      · show lo ≤ (x.spansFrom q.2).2
        rw [spansFrom_snd]
        exact Nat.le_trans hlo (Nat.le_add_right q.2 x.width)
      · intro s hs
        have hsplit : s ∈ q.1 ∨ s ∈ (x.spansFrom q.2).1 := by
          have hs' : s ∈ q.1 ++ (x.spansFrom q.2).1 := hs
          simpa using hs'
        show lo ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ (x.spansFrom q.2).2
        rw [spansFrom_snd]
        rcases hsplit with h | h
        · obtain ⟨h1, h2, h3⟩ := hq s h
          exact ⟨h1, h2, Nat.le_trans h3 (Nat.le_add_right q.2 x.width)⟩
        · obtain ⟨h1, h2, h3⟩ := ih x (by simp) q.2 s h
          exact ⟨Nat.le_trans hlo h1, h2, h3⟩

/-- Every span recorded by `spansFrom` is nonempty and lies inside `[start, start + width]`. -/
theorem spansFrom_mem_bounds (t : Tree) :
    ∀ start s, s ∈ (t.spansFrom start).1 →
      start ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ start + t.width := by
  induction t using inductionOn with
  | leaf w =>
      intro start s hs
      rw [spansFrom_leaf] at hs
      simp at hs
  | node c child children ih ihs =>
      intro start s hs
      rw [spansFrom_node_fst] at hs
      have hstop : (children.foldl spanStep (child.spansFrom start)).2
          = start + (Tree.node c child children).width := by
        rw [← spansFrom_node_snd, spansFrom_snd]
      have hs' : s = (c, start, (children.foldl spanStep (child.spansFrom start)).2)
          ∨ s ∈ (children.foldl spanStep (child.spansFrom start)).1 := by
        simpa using hs
      rcases hs' with rfl | hmem
      · rw [hstop]
        have hw := width_pos (Tree.node c child children)
        exact ⟨Nat.le_refl start, Nat.lt_add_of_pos_right hw, Nat.le_refl _⟩
      · rw [← Array.foldl_toList] at hmem
        have hres := spansFold_mem children.toList
          (fun x hx ↦ ihs x (by simpa using hx))
          (child.spansFrom start) start
          (by rw [spansFrom_snd]; exact Nat.le_add_right start child.width)
          (fun s' hs' ↦ by rw [spansFrom_snd]; exact ih start s' hs')
          s hmem
        rwa [Array.foldl_toList, hstop] at hres

/-- Every span recorded by `spans` is nonempty and lies inside `[start, start + width]`. -/
theorem spans_mem_bounds (t : Tree) (start : Nat) (s : Cat × Nat × Nat)
    (hs : s ∈ t.spans start) :
    start ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ start + t.width :=
  spansFrom_mem_bounds t start s hs

end Tree
end Nlp
