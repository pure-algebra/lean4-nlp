/-!
# Text spans and identifiers

Small value types shared by the annotation and model layers. Spans use half-open UTF-8 byte
offsets into the original document text; they deliberately do not depend on Lean's evolving
`String.Pos` interface.
-/

namespace Nlp

/-- A half-open byte range `[b, e)` into a document's original UTF-8 text. -/
structure Span where
  b : Nat
  e : Nat
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- A span is well formed when its start does not follow its end. -/
def Span.WF (span : Span) : Prop := span.b ≤ span.e

instance (span : Span) : Decidable span.WF := by
  unfold Span.WF
  infer_instance

/-- Token index inside a document. -/
def TokId := Nat
  deriving Repr, DecidableEq, Inhabited, Hashable, ToString

/-- Sentence index inside a document. -/
def SentId := Nat
  deriving Repr, DecidableEq, Inhabited, Hashable, ToString

/-- Interned vocabulary or tag-set symbol index. -/
def SymbolId := UInt32
  deriving Repr, DecidableEq, Inhabited, Hashable

end Nlp
