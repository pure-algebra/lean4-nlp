import Nlp.Core.Doc

/-!
# Statically indexed annotators

An `Ann M requires produces` runs on any document containing `requires`, preserves unrelated
layers, and prepends `produces` to the result index. The hot-path specialization uses `M = Id`.
-/

namespace Nlp

/-- Layers in `xs` that are not already supplied by `ys`. -/
def diff (xs ys : Layers) : Layers := xs.filter fun layer ↦ !(ys.contains layer)

theorem sub_of_diff {required produced available : Layers}
    (h : Sub (diff required produced) available) :
    Sub required (produced ++ available) := by
  intro layer present
  by_cases supplied : layer ∈ produced
  · exact List.mem_append_left available supplied
  · refine List.mem_append_right produced (h layer ?_)
    simp [diff, List.mem_filter, present, supplied]

/-- An annotator with effects `M`, required layers `requires`, and produced layers `produces`. -/
structure Ann (M : Type → Type) (requires produces : Layers) where
  name : String
  run : {available : Layers} →
    Sub requires available → Doc available → M (Doc (produces ++ available))

namespace Ann

/-- The no-op annotator. -/
def id [Pure M] : Ann M [] [] where
  name := "id"
  run := fun _ doc ↦ pure doc

/-- Sequential annotator composition.

Only requirements not produced by the first annotator remain requirements of the composition.
The index cast is erased because the document index is phantom.
-/
def seq [Monad M] (first : Ann M requires₁ produces₁)
    (second : Ann M requires₂ produces₂) :
    Ann M (requires₁ ++ diff requires₂ produces₁) (produces₂ ++ produces₁) where
  name := first.name ++ ";" ++ second.name
  run := fun {available} requirements doc ↦ do
    let firstRequirements : Sub requires₁ available :=
      fun layer present ↦ requirements layer (List.mem_append_left _ present)
    let remainingRequirements : Sub (diff requires₂ produces₁) available :=
      fun layer present ↦ requirements layer (List.mem_append_right _ present)
    let afterFirst ← first.run firstRequirements doc
    let afterSecond ← second.run (sub_of_diff remainingRequirements) afterFirst
    pure (List.append_assoc produces₂ produces₁ available ▸ afterSecond)

/-- Run an annotator while asking the elaborator to discharge its requirements. -/
@[inline] def apply (ann : Ann M requires produces) (doc : Doc available)
    (requirements : Sub requires available := by decide) : M (Doc (produces ++ available)) :=
  ann.run requirements doc

end Ann

infixl:55 " ⋙ " => Ann.seq

end Nlp
