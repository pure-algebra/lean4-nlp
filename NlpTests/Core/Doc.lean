import Nlp.Core.Doc

namespace NlpTests.Core.Doc

open Nlp

private def spans : Array Span := #[⟨0, 3⟩, ⟨4, 8⟩]
private def forms : Array String := #["the", "dogs"]

private def tokenDoc : Doc [.tokens] := { text := "the dogs", spans, forms }

example : tokenDoc.WF := by decide

example : tokenDoc.size = 2 := by decide

example : tokenDoc.formAt 0 = "the" := by decide

example : tokenDoc.spanAt 1 = ⟨4, 8⟩ := by decide

example : (Doc.empty "text").WF := Doc.empty_wf "text"

example : Doc.checked tokenDoc = .ok tokenDoc := by rfl

private def malformed : Doc [.tokens] :=
  { text := "the dogs", spans := #[⟨0, 3⟩], forms }

example : ¬ malformed.WF := by decide

example :
    Doc.checked malformed =
      .error (.invalidColumnSizes
        { forms := 2, spans := 1, pos := 0, lemma := 0, ner := 0, head := 0, deprel := 0 }) := by
  rfl

example : Doc.ofTokens "the dogs" spans forms = .ok tokenDoc := by rfl

private def tagged : Doc [.pos, .tokens] :=
  { tokenDoc with pos := #["DET", "NOUN"] }

example : tagged.WF := by decide

example : tagged.posAt 1 = "NOUN" := by decide

end NlpTests.Core.Doc
