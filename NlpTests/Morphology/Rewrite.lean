import Nlp.Morphology.Rewrite

namespace NlpTests.Morphology.Rewrite

open Nlp.Morphology

example : Pos.ofTag "NOUN" = .noun := by decide
example : Pos.ofTag "NNP" = .properNoun := by decide
example : Pos.ofTag "VBZ" = .verb := by native_decide
example : Pos.ofTag "AUX" = .auxiliary := by decide
example : Pos.ofTag "JJS" = .adjective := by native_decide
example : Pos.ofTag "RBR" = .adverb := by native_decide
example : Pos.ofTag "PART" = .particle := by decide
example : Pos.ofTag "PUNCT" = .other := by native_decide

private def plural : Nlp.Morphology.Rewrite := ⟨"s", ""⟩
private def dogs : Derivation := ⟨"dog", plural⟩

example : plural.analyze? "dogs" = some dogs := by native_decide
example : dogs.surface = "dogs" := by decide
example : dogs.lemma = "dog" := by decide

example (derivation : Derivation) (found : plural.analyze? "dogs" = some derivation) :
    derivation.surface = "dogs" :=
  plural.surface_eq_of_analyze?_eq_some "dogs" derivation found

example : plural.generate? "dog" = some dogs := by native_decide

example (derivation : Derivation) (found : plural.generate? "dog" = some derivation) :
    derivation.lemma = "dog" :=
  plural.lemma_eq_of_generate?_eq_some "dog" derivation found

example : plural.inverse.inverse = plural := Nlp.Morphology.Rewrite.inverse_inverse plural
example : dogs.reverse.reverse = dogs := Derivation.reverse_reverse dogs
example : dogs.reverse.surface = dogs.lemma := Derivation.surface_reverse dogs
example : dogs.reverse.lemma = dogs.surface := Derivation.lemma_reverse dogs

end NlpTests.Morphology.Rewrite
