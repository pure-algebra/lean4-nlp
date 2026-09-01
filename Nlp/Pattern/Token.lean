import Nlp.Core.Doc

/-!
# Typed token predicates

Token predicates are a first-order, serializable alternative to reflection over annotation keys.
They inspect document columns directly by token index, so matching does not allocate token-view
records or sentence slices. The safe evaluator rejects unadvertised columns even when stale raw
storage is present. Checked RegexNER sessions use the explicitly unchecked hot-path evaluator only
after validating every dynamically required layer once.
-/

namespace Nlp.Pattern

/-- A deterministic test over one token-column string value. -/
inductive TextTest where
  /-- Accept every present value. -/
  | any
  /-- Accept one exact, case-sensitive value. -/
  | equal (value : String)
  /-- Accept any value with the exact case-sensitive prefix. -/
  | prefix (value : String)
  /-- Accept any value with the exact case-sensitive suffix. -/
  | suffix (value : String)
  /-- Accept membership in a caller-ordered exact vocabulary. -/
  | oneOf (values : Array String)
  deriving Repr, DecidableEq, Inhabited

namespace TextTest

/-- Evaluate a first-order string test without changing its source value. -/
@[inline] def accepts : TextTest → String → Bool
  | .any, _ => true
  | .equal expected, found => found == expected
  | .prefix expected, found => found.startsWith expected
  | .suffix expected, found => found.endsWith expected
  | .oneOf expected, found => expected.contains found

end TextTest

/-- Boolean token predicates over statically named document columns. -/
inductive TokenAtom where
  /-- Test the exact source-preserving token form. -/
  | form (test : TextTest)
  /-- Test the part-of-speech column. -/
  | pos (test : TextTest)
  /-- Test the lemma column. -/
  | lemma (test : TextTest)
  /-- Test the existing flat named-entity column. -/
  | ner (test : TextTest)
  /-- Conjoin two token-local predicates. -/
  | both (left right : TokenAtom)
  /-- Disjoin two token-local predicates. -/
  | either (left right : TokenAtom)
  /-- Negate one token-local predicate. -/
  | negate (atom : TokenAtom)
  deriving Repr, DecidableEq, Inhabited

namespace TokenAtom

/-- Insert one required layer exactly once while retaining first-occurrence order. -/
private def insertLayer (layers : Layers) (layer : Layer) : Layers :=
  if layer ∈ layers then layers else layers ++ [layer]

/-- Stable set union for the small annotation-layer universe. -/
private def unionLayers (left right : Layers) : Layers :=
  right.foldl insertLayer left

/-- Annotation layers read by one token predicate. -/
def requiredLayers : TokenAtom → Layers
  | .form _ => [.tokens]
  | .pos _ => [.tokens, .pos]
  | .lemma _ => [.tokens, .lemma]
  | .ner _ => [.tokens, .ner]
  | .both left right | .either left right =>
      unionLayers left.requiredLayers right.requiredLayers
  | .negate atom => atom.requiredLayers

/-- Test whether a statically indexed document advertises every field read by an atom. -/
def requirementsSatisfied (atom : TokenAtom) (available : Layers) : Bool :=
  atom.requiredLayers.all fun layer ↦ decide (layer ∈ available)

/--
Evaluate directly against raw document columns after an enclosing boundary validated requirements.

This avoids repeating the small dynamic layer-set check at every NFA transition. Direct callers
should normally use `holdsAt`, which rejects stale unadvertised columns.
-/
def holdsAtUnchecked (doc : Doc available) : TokenAtom → Nat → Bool
  | .form test, index => (doc.forms[index]?).any test.accepts
  | .pos test, index => (doc.pos[index]?).any test.accepts
  | .lemma test, index => (doc.lemma[index]?).any test.accepts
  | .ner test, index => (doc.ner[index]?).any test.accepts
  | .both left right, index =>
      left.holdsAtUnchecked doc index && right.holdsAtUnchecked doc index
  | .either left right, index =>
      left.holdsAtUnchecked doc index || right.holdsAtUnchecked doc index
  | .negate atom, index => !atom.holdsAtUnchecked doc index

/-- Evaluate one token predicate only when its annotation layers are advertised. -/
@[inline] def holdsAt (doc : Doc available) (atom : TokenAtom) (index : Nat) : Bool :=
  atom.requirementsSatisfied available && atom.holdsAtUnchecked doc index

end TokenAtom

end Nlp.Pattern
