import Nlp.IO.ConlluReader
import Nlp.Pipeline.Morphology

namespace NlpTests.Pipeline.Morphology

open Nlp

private def lexemes : Array Nlp.Morphology.Lexeme :=
  #[⟨.noun, "dog"⟩, ⟨.verb, "run"⟩, ⟨.verb, "go"⟩, ⟨.auxiliary, "can"⟩,
    ⟨.particle, "not"⟩]

private def exceptions : Array Nlp.Morphology.ExceptionEntry :=
  #[⟨.auxiliary, "ca", "can"⟩, ⟨.particle, "n't", "not"⟩]

private def model : Nlp.Morphology.Model :=
  match Nlp.Morphology.Model.compile lexemes exceptions with
  | .ok value => value
  | .error _ => Nlp.Morphology.Model.empty

private def tagged : Doc [.pos, .tokens] :=
  { text := "dogs run", spans := #[⟨0, 4⟩, ⟨5, 8⟩], forms := #["dogs", "run"],
    pos := #["NOUN", "VERB"] }

example : tagged.SemanticWF := by native_decide

example : (model.lemmatizeForms #["dogs", "run", "unknown"] #["NOUN", "VERB"]).size = 3 :=
  by decide

example : model.lemmatizeForms #["dogs", "run", "unknown"] #["NOUN", "VERB"] =
    #["dog", "run", "unknown"] := by
  native_decide

example :
    (model.lemmatizeForms tagged.forms tagged.pos)[1] =
      model.lemmaOrSelf (Nlp.Morphology.Pos.ofTag tagged.pos[1]!) tagged.forms[1] :=
  model.lemmatizeForms_getElem tagged.forms tagged.pos 1 (by decide)

private def lemmatized := model.lemmatizeDoc tagged

example : lemmatized.lemma = #["dog", "run"] := by native_decide
example : lemmatized.text = tagged.text := by rfl
example : lemmatized.spans = tagged.spans := by rfl
example : lemmatized.pos = tagged.pos := by rfl
example : lemmatized.WF := model.lemmatizeDoc_wf tagged (by native_decide)
example : lemmatized.SemanticWF :=
  model.lemmatizeDoc_semanticWF tagged (by native_decide)

example : (model.annotator.run (by decide) tagged).lemma = #["dog", "run"] := by
  native_decide

private def conlluSample : String :=
  "# text = can't go\n" ++
    "1\tca\tcan\tAUX\tMD\t_\t3\taux\t3:aux\tSpaceAfter=No\n" ++
    "2\tn't\tnot\tPART\tRB\t_\t3\tadvmod\t3:advmod\t_\n" ++
    "3\tgo\tgo\tVERB\tVB\t_\t0\troot\t0:root\t_\n\n"

private def predictsConlluGold : Bool :=
  match Nlp.IO.parseConllu conlluSample with
  | .ok sentences =>
    match sentences[0]? with
    | some sentence =>
      match sentence.toDoc with
      | .ok document =>
        let predicted := model.lemmatizeDoc document
        predicted.lemma == document.lemma && decide predicted.SemanticWF
      | .error _ => false
    | none => false
  | .error _ => false

#guard predictsConlluGold

private def malformed : Doc [.pos, .tokens] :=
  { tagged with pos := #["NOUN"] }

private def testSingle : IO Unit := do
  match ← NLP.runIO {} <| NLP.lemmatize model tagged with
  | .ok output =>
    if output.lemma != #["dog", "run"] || output.text != tagged.text then
      throw <| IO.userError "effectful morphology changed the pure result"
  | .error cause => throw <| IO.userError s!"valid morphology input failed: {cause}"

private def testMalformed : IO Unit := do
  match ← NLP.runIO {} <| NLP.lemmatize model malformed with
  | .error (.invalidInput "lemmatizer input" _) => pure ()
  | _ => throw <| IO.userError "malformed morphology input crossed the checked boundary"

private def testModelFailure : IO Unit := do
  match ← NLP.runIO {} <|
      NLP.compileMorphologyModel #[⟨.noun, ""⟩] #[] "models/english-morphology" with
  | .error (.modelCorrupt "models/english-morphology" why) =>
    if why != "lexeme 0 has an empty base form" then
      throw <| IO.userError "morphology model failure lost its actionable detail"
  | _ => throw <| IO.userError "invalid morphology data crossed the checked model boundary"

private def taggedWord (word tag : String) : Doc [.pos, .tokens] :=
  { text := word, spans := #[⟨0, word.utf8ByteSize⟩], forms := #[word], pos := #[tag] }

private def testOrderedBatch : IO Unit := do
  let documents :=
    #[taggedWord "dogs" "NOUN", taggedWord "run" "VERB", taggedWord "ca" "AUX",
      taggedWord "n't" "PART"]
  let config : Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config <| NLP.lemmatizeManyWithMinTokens 1 model documents with
  | .ok output =>
    if output.map (fun doc ↦ doc.lemma[0]!) != #["dog", "run", "can", "not"] then
      throw <| IO.userError "parallel morphology lost input order or a pure result"
  | .error cause => throw <| IO.userError s!"parallel morphology failed: {cause}"

private def testCancelled : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.lemmatize model tagged)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "morphology lost its cancellation reason"

#eval testSingle
#eval testMalformed
#eval testModelFailure
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.Morphology
