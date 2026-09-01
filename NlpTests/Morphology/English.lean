import Nlp.Morphology.English

namespace NlpTests.Morphology.English

open Nlp.Morphology

private def lexemes : Array Lexeme :=
  #[⟨.noun, "dog"⟩, ⟨.noun, "box"⟩, ⟨.noun, "city"⟩, ⟨.noun, "child"⟩,
    ⟨.noun, "axe"⟩, ⟨.noun, "axis"⟩, ⟨.verb, "run"⟩, ⟨.verb, "make"⟩,
    ⟨.verb, "study"⟩, ⟨.auxiliary, "can"⟩, ⟨.auxiliary, "will"⟩,
    ⟨.adjective, "large"⟩, ⟨.adjective, "quick"⟩, ⟨.particle, "not"⟩]

private def exceptions : Array ExceptionEntry :=
  #[⟨.noun, "children", "child"⟩, ⟨.noun, "axes", "axe"⟩,
    ⟨.noun, "axes", "axis"⟩, ⟨.auxiliary, "ca", "can"⟩,
    ⟨.auxiliary, "wo", "will"⟩, ⟨.particle, "n't", "not"⟩,
    ⟨.verb, "running", "run"⟩]

private def compiled : Except CompileError Model :=
  Model.compile lexemes exceptions

private def model : Model :=
  match compiled with
  | .ok value => value
  | .error _ => Model.empty

example : compiled.isOk := by native_decide

private def compileError? : Except CompileError Model → Option CompileError
  | .ok _ => none
  | .error cause => some cause

example : compileError? (Model.compile #[⟨.noun, ""⟩] #[]) = some (.emptyLexeme 0) := by
  native_decide

example :
    compileError? (Model.compile #[] #[⟨.noun, "", "word"⟩]) =
      some (.emptyExceptionSurface 0) := by
  native_decide

example :
    compileError? (Model.compile #[] #[⟨.noun, "words", ""⟩]) =
      some (.emptyExceptionLemma 0) := by
  native_decide

example : model.lemma? .noun "dogs" = some "dog" := by native_decide
example : model.lemma? .noun "boxes" = some "box" := by native_decide
example : model.lemma? .noun "cities" = some "city" := by native_decide
example : model.lemma? .verb "running" = some "run" := by native_decide
example : model.lemma? .verb "making" = some "make" := by native_decide
example : model.lemma? .verb "studies" = some "study" := by native_decide
example : model.lemma? .adjective "larger" = some "large" := by native_decide
example : model.lemma? .adjective "quickest" = some "quick" := by native_decide

example : (model.analyses .noun "axes").map Analysis.lemma = #["axe", "axis"] := by
  native_decide

example : (model.analyses .noun "axes").all fun analysis ↦
    analysis.origin == .exception := by
  native_decide

example : model.lemma? .properNoun "Hughes" = none := by native_decide
example : model.lemmaOrSelf .properNoun "Hughes" = "Hughes" := by native_decide
example : model.lemmaOrSelf .other "😀" = "😀" := by native_decide
example : model.lemmaOrSelf .noun "gas" = "gas" := by native_decide

example : model.lemma? .auxiliary "ca" = some "can" := by native_decide
example : model.lemma? .auxiliary "wo" = some "will" := by native_decide
example : model.lemma? .particle "n't" = some "not" := by native_decide

example : (English.derivations .noun "boxes").all fun derivation ↦
    derivation.surface == "boxes" := by
  native_decide

example : (English.generations .noun "box").all fun derivation ↦
    derivation.lemma == "box" := by
  native_decide

example : English.generations .noun "" = #[] := by native_decide
example : Model.empty.generate .noun "" = #[] := by native_decide

example : (model.generate .noun "child").map Analysis.surface =
    #["children", "child", "childs"] := by
  native_decide

example : (model.generate .noun "box").map Analysis.surface =
    #["box", "boxs", "boxes"] := by
  native_decide

end NlpTests.Morphology.English
