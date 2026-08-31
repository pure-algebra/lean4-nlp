/-!
# Annotation layers

The list of completed core annotation layers is a phantom index on `Nlp.Doc`. Requirements are
ordinary propositions over these lists and are decidable at elaboration time for closed indices.
-/

namespace Nlp

/-- Coarse, annotator-shaped layers tracked statically by `Doc`. -/
inductive Layer where
  | tokens
  | sents
  | pos
  | lemma
  | ner
  | dep
  | parse
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- A presentation of the finite set of completed annotation layers. -/
abbrev Layers := List Layer

/-- Every layer required by `xs` occurs among the available layers `ys`. -/
def Sub (xs ys : Layers) : Prop := ∀ layer ∈ xs, layer ∈ ys

instance instDecidableSub (xs ys : Layers) : Decidable (Sub xs ys) := by
  unfold Sub
  infer_instance

theorem sub_refl (xs : Layers) : Sub xs xs := fun _ present ↦ present

theorem sub_trans {xs ys zs : Layers} (hxy : Sub xs ys) (hyz : Sub ys zs) : Sub xs zs :=
  fun layer present ↦ hyz layer (hxy layer present)

theorem sub_append_left {xs ys : Layers} : Sub xs (xs ++ ys) :=
  fun _ present ↦ List.mem_append_left ys present

theorem sub_append_right {xs ys : Layers} : Sub ys (xs ++ ys) :=
  fun _ present ↦ List.mem_append_right xs present

end Nlp
