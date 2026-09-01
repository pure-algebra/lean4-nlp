import Nlp.Pattern.Token

/-! # Typed token-predicate tests -/

namespace NlpTests.Pattern.Token

open Nlp Nlp.Pattern

/-- Fully populated document columns for first-order predicate checks. -/
private def document : Doc [.ner, .lemma, .pos, .tokens] :=
  { text := "Dogs run"
    forms := #["Dogs", "run"]
    spans := #[⟨0, 4⟩, ⟨5, 8⟩]
    pos := #["NNS", "VBP"]
    lemma := #["dog", "run"]
    ner := #["ANIMAL", "O"] }

example : (TokenAtom.form (.equal "Dogs")).holdsAt document 0 = true := by native_decide
example : (TokenAtom.form (.prefix "Do")).holdsAt document 0 = true := by native_decide
example : (TokenAtom.form (.suffix "gs")).holdsAt document 0 = true := by native_decide
example : (TokenAtom.form (.oneOf #["cats", "Dogs"])).holdsAt document 0 = true := by
  native_decide

example : (TokenAtom.both (.pos (.equal "NNS")) (.lemma (.equal "dog"))).holdsAt
    document 0 = true := by
  native_decide

example : (TokenAtom.either (.ner (.equal "PERSON")) (.ner (.equal "ANIMAL"))).holdsAt
    document 0 = true := by
  native_decide

example : (TokenAtom.negate (.form (.equal "cats"))).holdsAt document 0 = true := by
  native_decide

/-- Out-of-bounds and absent optional columns cannot satisfy a positive field test. -/
example : (TokenAtom.form .any).holdsAt document 2 = false := by native_decide

private def tokenOnly : Doc [.tokens] :=
  { text := "Dogs", forms := #["Dogs"], spans := #[⟨0, 4⟩] }

example : (TokenAtom.pos .any).holdsAt tokenOnly 0 = false := by native_decide

/-- Safe evaluation ignores stale raw storage for a layer absent from the phantom index. -/
private def stalePos : Doc [.tokens] :=
  { tokenOnly with pos := #["NNS"] }

example : (TokenAtom.pos .any).holdsAt stalePos 0 = false := by native_decide

/-- The unchecked evaluator is reserved for boundaries that validated dynamic requirements. -/
example : (TokenAtom.pos .any).holdsAtUnchecked stalePos 0 = true := by native_decide

/-- Required layers are stable, duplicate-free, and reflect boolean composition. -/
example : (TokenAtom.both (.lemma .any) (.both (.pos .any) (.lemma .any))).requiredLayers =
    [.tokens, .lemma, .pos] := by
  native_decide

example : (TokenAtom.ner .any).requirementsSatisfied [.ner, .tokens] = true := by
  native_decide

example : (TokenAtom.ner .any).requirementsSatisfied [.tokens] = false := by
  native_decide

end NlpTests.Pattern.Token
