import Nlp.Pipeline.Ann

namespace NlpTests.Pipeline.Ann

open Nlp

private def tokenize : Ann Id [] [.tokens] where
  name := "tokenize"
  run := fun _ doc ↦
    { doc with
      spans := #[⟨0, 4⟩]
      forms := #["dogs"] }

private def tag : Ann Id [.tokens] [.pos] where
  name := "pos"
  run := fun _ doc ↦ { doc with pos := #["NNS"] }

private def lemmatize : Ann Id [.tokens, .pos] [.lemma] where
  name := "lemma"
  run := fun _ doc ↦ { doc with lemma := #["dog"] }

private def inferredPipeline := tokenize ⋙ tag ⋙ lemmatize

private def pipeline : Ann Id [] [.lemma, .pos, .tokens] := inferredPipeline

private def result : Doc [.lemma, .pos, .tokens] :=
  pipeline.apply (Doc.empty "dogs")

example : result.formAt 0 = "dogs" := by decide

example : result.posAt 0 = "NNS" := by decide

example : result.lemmaAt 0 = "dog" := by decide

example : result.WF := by decide

example : inferredPipeline.name = "tokenize;pos;lemma" := by decide

example : diff [.tokens, .pos] [.pos] = [.tokens] := by decide

example : Sub (diff [.tokens, .pos] [.pos]) [.tokens] := by decide

end NlpTests.Pipeline.Ann
