import Nlp.Core.Algebra.BigOps
import Nlp.Core.Engine.Inside

/-!
# Functional restatement of the inside sweep

`Nlp.inside` is an imperative single-pass kernel.  This module proves that it equals a plain
`Array.foldl` over the edge list (`inside_eq_insideFold`), so all further semantic reasoning —
the hyperpath-sum specification, topological-order invariants — can proceed by ordinary
induction on edges instead of loop reasoning.  Two first consequences are proved here: the
value table keeps its size, and a node that no edge targets keeps the semiring zero.
-/

namespace Nlp

variable {K : Type} [SemiringOps K]

/-- The weight an edge contributes given the current node values: its own weight times the
values of its tails, in tail order. -/
def Edge.contribution (values : Array K) (edge : Edge K) : K :=
  edge.tails.foldl (fun contribution tail ↦ contribution * values.getD tail.toNat 0) edge.w

/-- Fold one edge into the value table: add its contribution onto its head node. -/
def insideStep (values : Array K) (edge : Edge K) : Array K :=
  values.set! edge.head.toNat (values.getD edge.head.toNat 0 + edge.contribution values)

/-- Functional restatement of the inside sweep. -/
def insideFold (n : Nat) (edges : Array (Edge K)) : Array K :=
  edges.foldl insideStep (Array.replicate n 0)

private theorem id_pure_eq {α : Type v} (a : α) : (pure a : Id α) = a := rfl

private theorem id_bind_eq {α β : Type v} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl

private theorem id_forIn_yield_eq_foldl {α : Type v} {β : Type w} (xs : Array α)
    (f : α → β → β) (init : β) :
    (forIn (m := Id) xs init fun a b ↦ ForInStep.yield (f a b)) =
      xs.foldl (fun b a ↦ f a b) init :=
  Array.forIn_pure_yield_eq_foldl f init

/-- **Kernel refinement.**  The imperative inside sweep is the functional edge fold. -/
theorem inside_eq_insideFold (n : Nat) (edges : Array (Edge K)) :
    inside n edges = insideFold n edges := by
  unfold inside
  simp only [Id.run, id_bind_eq, id_pure_eq, id_forIn_yield_eq_foldl]
  rfl

private theorem foldl_insideStep_size (edges : List (Edge K)) (values : Array K) :
    (edges.foldl insideStep values).size = values.size := by
  induction edges generalizing values with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    simp [insideStep, Array.set!]

/-- The value table always has one entry per node. -/
theorem insideFold_size (n : Nat) (edges : Array (Edge K)) : (insideFold n edges).size = n := by
  unfold insideFold
  rw [← Array.foldl_toList, foldl_insideStep_size]
  exact Array.size_replicate

/-- The imperative kernel also returns one entry per node. -/
theorem inside_size (n : Nat) (edges : Array (Edge K)) : (inside n edges).size = n :=
  (inside_eq_insideFold n edges) ▸ insideFold_size n edges

private theorem foldl_insideStep_getD (edges : List (Edge K)) (values : Array K) (v : Nat)
    (h : ∀ edge ∈ edges, edge.head.toNat ≠ v) :
    (edges.foldl insideStep values).getD v 0 = values.getD v 0 := by
  induction edges generalizing values with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih _ fun x hx ↦ h x (List.mem_cons_of_mem e hx)]
    simp [insideStep, Array.set!, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne (h e List.mem_cons_self)]

/-- A node that no edge targets keeps the semiring zero. -/
theorem inside_getD_of_not_head (n : Nat) (edges : Array (Edge K)) (v : Nat)
    (h : ∀ edge ∈ edges, edge.head.toNat ≠ v) :
    (inside n edges).getD v 0 = 0 := by
  rw [inside_eq_insideFold]
  unfold insideFold
  rw [← Array.foldl_toList,
    foldl_insideStep_getD edges.toList _ v fun edge hx ↦ h edge (Array.mem_def.mpr hx)]
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-! ## The recurrence characterization

Under the topological ordering and in-bounds preconditions, every node's final value satisfies
the inside recurrence: it is the accumulation, over its incoming edges in sweep order, of the
edge weight times the *final* values of the edge's tails.  Because the right-hand side
accumulates in exactly the kernel's order, the theorem needs **no algebraic laws**: it holds
for every `SemiringOps` carrier, lawless `Float` carriers included.
-/

private theorem foldl_mul_congr (l : List UInt32) (values values' : Array K)
    (h : ∀ tail ∈ l, values.getD tail.toNat 0 = values'.getD tail.toNat 0) :
    ∀ acc : K,
      l.foldl (fun c tail ↦ c * values.getD tail.toNat 0) acc =
        l.foldl (fun c tail ↦ c * values'.getD tail.toNat 0) acc := by
  induction l with
  | nil => intro acc; rfl
  | cons t ts ih =>
    intro acc
    rw [List.foldl_cons, List.foldl_cons, h t List.mem_cons_self,
      ih (fun x hx ↦ h x (List.mem_cons_of_mem t hx))]

private theorem contribution_congr (edge : Edge K) (values values' : Array K)
    (h : ∀ tail ∈ edge.tails, values.getD tail.toNat 0 = values'.getD tail.toNat 0) :
    edge.contribution values = edge.contribution values' := by
  unfold Edge.contribution
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_mul_congr edge.tails.toList values values'
    (fun tail ht ↦ h tail (Array.mem_def.mpr ht)) edge.w

omit [SemiringOps K] in
/-- No edge at or after the consumer of a tail can produce that tail. -/
private theorem drop_no_producer (edges : Array (Edge K)) (htopo : EdgesTopological edges)
    (m : Nat) (hm : m < edges.size) (t : UInt32) (ht : t ∈ (edges[m]'hm).tails) :
    ∀ e ∈ edges.toList.drop m, e.head.toNat ≠ t.toNat := by
  intro e he heq
  obtain ⟨i, hi, hei⟩ := List.getElem_of_mem he
  rw [List.getElem_drop] at hei
  have hmi : m + i < edges.size := by
    have := hi
    simp [List.length_drop, Array.length_toList] at this
    omega
  have hhead : (edges[m + i]'hmi).head = t := by
    have : edges.toList[m + i]'(by simpa [Array.length_toList] using hmi) = edges[m + i]'hmi :=
      Array.getElem_toList _
    rw [this] at hei
    rw [← hei] at heq
    exact UInt32.toNat_inj.mp heq
  have := htopo m hm t ht (m + i) hmi hhead
  omega

private theorem insideStep_getD_ne (values : Array K) (edge : Edge K) (v : Nat)
    (h : edge.head.toNat ≠ v) : (insideStep values edge).getD v 0 = values.getD v 0 := by
  unfold insideStep
  simp [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

private theorem insideStep_getD_self (values : Array K) (edge : Edge K)
    (h : edge.head.toNat < values.size) :
    (insideStep values edge).getD edge.head.toNat 0 =
      values.getD edge.head.toNat 0 + edge.contribution values := by
  unfold insideStep
  simp [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt h]

/-- After a prefix of the sweep, each node's value is the head-matching accumulation over that
prefix, with every contribution already at its final value. -/
private theorem insideFold_prefix (n : Nat) (edges : Array (Edge K))
    (htopo : EdgesTopological edges) (hbounds : EdgesInBounds n edges) :
    ∀ (m : Nat), m ≤ edges.size → ∀ v : Nat,
      ((edges.toList.take m).foldl insideStep (Array.replicate n 0)).getD v 0 =
        (edges.toList.take m).foldl
          (fun acc edge ↦
            if edge.head.toNat = v then acc + edge.contribution (insideFold n edges) else acc)
          0 := by
  intro m
  induction m with
  | zero =>
    intro _ v
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  | succ k ih =>
    intro hk v
    have hklt : k < edges.size := by omega
    have hktl : k < edges.toList.length := by simpa [Array.length_toList] using hklt
    rw [List.take_add_one, List.getElem?_eq_getElem hktl]
    simp only [Option.toList_some]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    have hedge : edges.toList[k]'hktl = edges[k]'hklt := Array.getElem_toList _
    rw [hedge]
    let prefixValues := (edges.toList.take k).foldl insideStep (Array.replicate n 0)
    have hpv :
        (edges.toList.take k).foldl insideStep (Array.replicate n 0) = prefixValues := rfl
    rw [hpv] at ih
    have hsize : prefixValues.size = n := by
      rw [← hpv, foldl_insideStep_size]
      exact Array.size_replicate
    have hcontrib :
        (edges[k]'hklt).contribution prefixValues =
          (edges[k]'hklt).contribution (insideFold n edges) := by
      refine contribution_congr _ _ _ fun tail htail ↦ ?_
      have hnoprod := drop_no_producer edges htopo k hklt tail htail
      have hfinal : insideFold n edges = (edges.toList.drop k).foldl insideStep prefixValues := by
        rw [← hpv, ← List.foldl_append, List.take_append_drop]
        unfold insideFold
        rw [← Array.foldl_toList]
      rw [hfinal, foldl_insideStep_getD _ _ _ hnoprod]
    by_cases hv : (edges[k]'hklt).head.toNat = v
    · subst hv
      rw [if_pos rfl, insideStep_getD_self prefixValues _ (hsize ▸ (hbounds k hklt).1),
        hcontrib, ih (by omega) _]
    · rw [if_neg hv, insideStep_getD_ne prefixValues _ v hv]
      exact ih (by omega) v

/--
**The inside recurrence.**  For a topologically ordered, in-bounds hypergraph, every node's
final value is the accumulation over its incoming edges — in sweep order — of the edge weight
times the final values of the edge's tails.  The right-hand side accumulates in exactly the
kernel's order, so no algebraic laws are required: this holds for every `SemiringOps` carrier,
including the lawless `Float` ones.
-/
theorem inside_recurrence (n : Nat) (edges : Array (Edge K))
    (htopo : EdgesTopological edges) (hbounds : EdgesInBounds n edges) (v : Nat) :
    (inside n edges).getD v 0 =
      edges.toList.foldl
        (fun acc edge ↦
          if edge.head.toNat = v then acc + edge.contribution (inside n edges) else acc)
        0 := by
  rw [inside_eq_insideFold]
  have hall := insideFold_prefix n edges htopo hbounds edges.size (Nat.le_refl _) v
  rw [show edges.toList.take edges.size = edges.toList by
      rw [← Array.length_toList]; exact List.take_length] at hall
  calc (insideFold n edges).getD v 0
      = (edges.toList.foldl insideStep (Array.replicate n 0)).getD v 0 := by
        unfold insideFold
        rw [← Array.foldl_toList]
    _ = _ := hall

end Nlp
