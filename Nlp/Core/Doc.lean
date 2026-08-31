import Nlp.Core.Data.Span
import Nlp.Core.Extra
import Nlp.Core.Layer

/-!
# Columnar annotated documents

`Doc ls` stores core annotations in parallel arrays while `ls` records which layers have run.
The index is phantom and the gated accessors erase their proof arguments. `Doc.WF` is checked at
input boundaries; it is intentionally not stored as a proof field on every document value.
-/

namespace Nlp

/-- A document with the completed annotation layers `ls`.

Core token annotations use a struct-of-arrays representation. The raw columns support efficient
functional record updates inside annotators; consumers should prefer the layer-gated accessors.
-/
structure Doc (ls : Layers) where
  text : String
  spans : Array Span := #[]
  forms : Array String := #[]
  sentEnd : Array Nat := #[]
  pos : Array String := #[]
  lemma : Array String := #[]
  ner : Array String := #[]
  head : Array Nat := #[]
  deprel : Array String := #[]
  extra : Extra := ∅

namespace Doc

/-- The number of token positions in a document. -/
@[inline] def size (doc : Doc ls) : Nat := doc.forms.size

/-- Column-size invariants for the layers represented by a document.

Token forms and spans always align. A completed token-level layer has exactly one entry per token;
dependency annotation has both a head and a relation entry per token. Sentence and parse layers
have sentence-level cardinalities and are intentionally outside this first predicate.
-/
def WF {ls : Layers} (doc : Doc ls) : Prop :=
  doc.spans.size = doc.size ∧
    (Layer.pos ∈ ls → doc.pos.size = doc.size) ∧
    (Layer.lemma ∈ ls → doc.lemma.size = doc.size) ∧
    (Layer.ner ∈ ls → doc.ner.size = doc.size) ∧
    (Layer.dep ∈ ls → doc.head.size = doc.size ∧ doc.deprel.size = doc.size)

instance instDecidableWF {ls : Layers} (doc : Doc ls) : Decidable doc.WF := by
  unfold WF
  infer_instance

/-- Counts reported when a document fails `Doc.WF`. -/
structure ColumnSizes where
  forms : Nat
  spans : Nat
  pos : Nat
  lemma : Nat
  ner : Nat
  head : Nat
  deprel : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A document failed boundary validation. -/
inductive ValidationError where
  | invalidColumnSizes (sizes : ColumnSizes)
  deriving Repr, DecidableEq, Inhabited

@[inline] private def columnSizes (doc : Doc ls) : ColumnSizes where
  forms := doc.forms.size
  spans := doc.spans.size
  pos := doc.pos.size
  lemma := doc.lemma.size
  ner := doc.ner.size
  head := doc.head.size
  deprel := doc.deprel.size

/-- Validate a document at an input or model boundary without changing its runtime shape. -/
def checked (doc : Doc ls) : Except ValidationError (Doc ls) :=
  if doc.WF then .ok doc else .error (.invalidColumnSizes (columnSizes doc))

theorem checked_eq_ok_iff (doc : Doc ls) : checked doc = .ok doc ↔ doc.WF := by
  by_cases wellFormed : doc.WF <;> simp [checked, wellFormed]

/-- Construct and validate the token layer produced by a tokenizer. -/
def ofTokens (text : String) (spans : Array Span) (forms : Array String) :
    Except ValidationError (Doc [.tokens]) :=
  checked { text, spans, forms }

/-- An empty, well-formed document before tokenization. -/
def empty (text : String) : Doc [] := { text }

theorem empty_wf (text : String) : (empty text).WF := by simp [empty, WF, size]

/-- Read a token form only from a document whose token layer is present. -/
@[inline] def formAt (doc : Doc ls) (i : Nat)
    (_needsTokens : Layer.tokens ∈ ls := by decide) : String :=
  doc.forms[i]!

/-- Read a token span only from a document whose token layer is present. -/
@[inline] def spanAt (doc : Doc ls) (i : Nat)
    (_needsTokens : Layer.tokens ∈ ls := by decide) : Span :=
  doc.spans[i]!

/-- Read a POS tag only from a document whose POS layer is present. -/
@[inline] def posAt (doc : Doc ls) (i : Nat)
    (_needsPos : Layer.pos ∈ ls := by decide) : String :=
  doc.pos[i]!

/-- Read a lemma only from a document whose lemma layer is present. -/
@[inline] def lemmaAt (doc : Doc ls) (i : Nat)
    (_needsLemma : Layer.lemma ∈ ls := by decide) : String :=
  doc.lemma[i]!

/-- Read an entity tag only from a document whose NER layer is present. -/
@[inline] def nerAt (doc : Doc ls) (i : Nat)
    (_needsNer : Layer.ner ∈ ls := by decide) : String :=
  doc.ner[i]!

/-- Read a dependency head only from a document whose dependency layer is present. -/
@[inline] def headAt (doc : Doc ls) (i : Nat)
    (_needsDep : Layer.dep ∈ ls := by decide) : Nat :=
  doc.head[i]!

/-- Read a dependency relation only from a document whose dependency layer is present. -/
@[inline] def deprelAt (doc : Doc ls) (i : Nat)
    (_needsDep : Layer.dep ∈ ls := by decide) : String :=
  doc.deprel[i]!

end Doc

end Nlp
