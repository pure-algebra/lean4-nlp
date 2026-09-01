import Nlp.Pipeline.English

namespace NlpTests.Pipeline.English

open Nlp Nlp.Sequence

private def cost (value : Float) : Cost := ⟨value⟩

private def hmm : Hmm where
  nTags := 2
  start := #[cost 0.0, cost 10.0]
  trans := #[cost 5.0, cost 0.0, cost 5.0, cost 0.0]
  emit := {}
  unk := #[cost 0.0, cost 0.0]

private def compiledTagger : Except PosTagger.CompileError PosTagger :=
  PosTagger.compile hmm #[] #["NOUN", "VERB"]

private def lexemes : Array Nlp.Morphology.Lexeme :=
  #[⟨.noun, "dog"⟩, ⟨.verb, "run"⟩]

private def morphology : Nlp.Morphology.Model :=
  match Nlp.Morphology.Model.compile lexemes #[] with
  | .ok model => model
  | .error _ => Nlp.Morphology.Model.empty

private def tokens : Doc [.tokens] :=
  { text := "dogs run", spans := #[⟨0, 4⟩, ⟨5, 8⟩], forms := #["dogs", "run"] }

private def sentences : Doc [.sents, .tokens] :=
  { tokens with sentEnd := #[1, 2] }

private def malformed : Doc [.tokens] :=
  { tokens with spans := #[⟨0, 4⟩] }

example (tagger : PosTagger) :
    (Nlp.English.tagAndLemmatizeDoc tagger morphology tokens).WF :=
  Nlp.English.tagAndLemmatizeDoc_wf tagger morphology tokens (by native_decide)

example (tagger : PosTagger) :
    (Nlp.English.tagAndLemmatizeDoc tagger morphology sentences).SemanticWF :=
  Nlp.English.tagAndLemmatizeDoc_semanticWF tagger morphology sentences
    (by native_decide)

private def pureCompositionWorks : Bool :=
  match compiledTagger with
  | .ok tagger =>
      let output := Nlp.English.tagAndLemmatizeDoc tagger morphology tokens
      let viaAnnotator :=
        (Nlp.English.tagAndLemmatizeAnnotator tagger morphology).run (by decide) tokens
      output.pos == #["NOUN", "VERB"] && output.lemma == #["dog", "run"] &&
        viaAnnotator.pos == output.pos && viaAnnotator.lemma == output.lemma
  | .error _ => false

#guard pureCompositionWorks

private def sentenceBoundariesReachTagger : Bool :=
  match compiledTagger with
  | .ok tagger =>
      let output := Nlp.English.tagAndLemmatizeDoc tagger morphology sentences
      output.pos == #["NOUN", "NOUN"] && output.lemma == #["dog", "run"]
  | .error _ => false

#guard sentenceBoundariesReachTagger

private def rawTextWorks : Bool :=
  match compiledTagger with
  | .ok tagger =>
      let output := Nlp.English.analyzeText .default tagger morphology "dogs run. dogs"
      output.forms == #["dogs", "run", ".", "dogs"] && output.sentEnd == #[3, 4] &&
        output.pos == #["NOUN", "VERB", "VERB", "NOUN"] &&
        output.lemma == #["dog", "run", ".", "dog"]
  | .error _ => false

#guard rawTextWorks

private def testSingle : IO Unit := do
  match ← NLP.runIO {} do
    let tagger ← NLP.compilePosTagger hmm #[] #["NOUN", "VERB"]
    NLP.tagAndLemmatize tagger morphology sentences
  with
  | .ok output =>
    if output.pos != #["NOUN", "NOUN"] || output.lemma != #["dog", "run"] then
      throw <| IO.userError "effectful English analysis changed the pure result"
  | .error cause => throw <| IO.userError s!"valid English input failed: {cause}"

private def testMalformed : IO Unit := do
  match ← NLP.runIO {} do
    let tagger ← NLP.compilePosTagger hmm #[] #["NOUN", "VERB"]
    NLP.tagAndLemmatize tagger morphology malformed
  with
  | .error (.invalidInput "English pipeline input" _) => pure ()
  | _ => throw <| IO.userError "malformed input crossed the fused checked boundary"

private def oneToken (word : String) : Doc [.tokens] :=
  { text := word, spans := #[⟨0, word.utf8ByteSize⟩], forms := #[word] }

private def testOrderedBatch : IO Unit := do
  let documents := #[oneToken "dogs", tokens, oneToken "run", oneToken "dogs"]
  let config : Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config do
    let tagger ← NLP.compilePosTagger hmm #[] #["NOUN", "VERB"]
    NLP.tagAndLemmatizeManyWithMinTokens 1 tagger morphology documents
  with
  | .ok output =>
    if output.map (fun doc ↦ doc.lemma) !=
        #[#["dog"], #["dog", "run"], #["run"], #["dog"]] then
      throw <| IO.userError "parallel English analysis lost input order or a pure result"
  | .error cause => throw <| IO.userError s!"parallel English analysis failed: {cause}"

private def testRawText : IO Unit := do
  match ← NLP.runIO {} do
    let tagger ← NLP.compilePosTagger hmm #[] #["NOUN", "VERB"]
    NLP.analyzeEnglishText .default tagger morphology "dogs run"
  with
  | .ok output =>
    if output.forms != #["dogs", "run"] || output.lemma != #["dog", "run"] then
      throw <| IO.userError "checked raw-text English analysis changed the pure result"
    if output.sentEnd != #[2] then
      throw <| IO.userError "raw-text English analysis lost its sentence boundary"
    if !decide output.SemanticWF then
      throw <| IO.userError "checked raw-text English analysis returned invalid output"
  | .error cause => throw <| IO.userError s!"raw-text English analysis failed: {cause}"

private def testCancelled : IO Unit := do
  let .ok tagger := compiledTagger
    | throw <| IO.userError "English cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.tagAndLemmatize tagger morphology tokens)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "English analysis lost its cancellation reason"

#eval testSingle
#eval testMalformed
#eval testOrderedBatch
#eval testRawText
#eval testCancelled

end NlpTests.Pipeline.English
