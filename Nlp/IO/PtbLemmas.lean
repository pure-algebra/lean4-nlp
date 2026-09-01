import Nlp.IO.Ptb

/-!
# PTB boundary facts

Small definitional laws document the two degenerate boundaries that do not require assumptions
about interned identifiers or printable tree shape.
-/

namespace Nlp.IO

/-- Parsing empty input succeeds without changing the interner and produces no trees. -/
theorem parseBracketed_empty (interner : Interner) :
    parseBracketed interner "" = .ok (interner, #[]) := by
  rfl

/-- A bare terminal cannot be represented as a complete bracketed PTB tree. -/
theorem renderBracketed_leaf (interner : Interner) (word : Word) :
    renderBracketed interner (.leaf word) = .error (.bareLeafRoot word) := by
  rfl

/-- A preterminal-shaped node cannot carry a second child. -/
theorem renderBracketed_preterminal_with_sibling (interner : Interner)
    (category : Cat) (first second : Word) :
    renderBracketed interner (.node category (.leaf first) #[.leaf second]) =
      .error (.invalidTreeShape category) := by
  simp [renderBracketed, Tree.para]

end Nlp.IO
