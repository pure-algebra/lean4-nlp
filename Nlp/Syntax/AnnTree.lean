/-!
# Annotated constituency trees

This is the strict-positivity-safe specialisation of a cofree-shaped tree used by the annotation
and parsing layers.
-/

namespace Nlp

mutual
  /-- A tree node paired with an annotation. -/
  inductive AnnTree (Ann : Type) (α : Type) where
    | mk (annotation : Ann) (body : AnnNode Ann α)

  /-- The unannotated functor layer of `AnnTree`. -/
  inductive AnnNode (Ann : Type) (α : Type) where
    | leaf (value : α)
    | node (label : String) (children : Array (AnnTree Ann α))
end

namespace AnnTree

/-- Extract the annotation at the root. -/
def ann : AnnTree Ann α → Ann
  | .mk annotation _ => annotation

/-- Extract the unannotated body at the root. -/
def body : AnnTree Ann α → AnnNode Ann α
  | .mk _ node => node

mutual
  /-- Fold an annotated tree. -/
  def cata (onLeaf : Ann → α → β)
      (onNode : Ann → String → Array β → β) : AnnTree Ann α → β
    | .mk annotation node => cataNode onLeaf onNode annotation node

  /-- Fold one body layer of an annotated tree. -/
  def cataNode (onLeaf : Ann → α → β)
      (onNode : Ann → String → Array β → β) (annotation : Ann) : AnnNode Ann α → β
    | .leaf value => onLeaf annotation value
    | .node label children =>
        onNode annotation label
          (children.attach.map fun ⟨tree, _⟩ => cata onLeaf onNode tree)
end

end AnnTree
end Nlp
