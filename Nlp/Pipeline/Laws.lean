import Nlp.Pipeline.Ann

/-!
# Annotator composition laws

At fixed input and output indices, annotators are precisely Kleisli arrows restricted to `Doc`
objects. Their identity and associativity laws therefore follow from `LawfulMonad`.
-/

namespace Nlp

/-- An index-fixed annotator arrow. -/
abbrev Arr (M : Type → Type) (input output : Layers) := Doc input → M (Doc output)

namespace Arr

/-- Kleisli identity restricted to documents. -/
def id (M : Type → Type) [Pure M] (layers : Layers) : Arr M layers layers := pure

/-- Kleisli composition restricted to documents. -/
def comp [Monad M] (first : Arr M input middle) (second : Arr M middle output) :
    Arr M input output :=
  fun doc ↦ first doc >>= second

theorem comp_id [Monad M] [LawfulMonad M] (arrow : Arr M input output) :
    comp arrow (id M output) = arrow := by
  funext doc
  simp [comp, id]

theorem id_comp [Monad M] [LawfulMonad M] (arrow : Arr M input output) :
    comp (id M input) arrow = arrow := by
  funext doc
  simp [comp, id]

theorem comp_assoc [Monad M] [LawfulMonad M]
    (first : Arr M firstLayers secondLayers)
    (second : Arr M secondLayers thirdLayers)
    (third : Arr M thirdLayers fourthLayers) :
    comp (comp first second) third = comp first (comp second third) := by
  funext doc
  show (first doc >>= second) >>= third = first doc >>= fun value ↦ second value >>= third
  rw [bind_assoc]

end Arr

end Nlp
