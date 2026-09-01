import Nlp.Pipeline.Ner

/-! Functional and effectful named-entity pipeline regression tests. -/

namespace NlpTests.Pipeline.Ner

open Nlp Nlp.Sequence

private def cost (value : Float) : Cost := ⟨value⟩

private def hmm : Hmm where
  nTags := 3
  start := #[cost 10.0, cost 0.0, cost 10.0]
  trans := #[
    cost 10.0, cost 10.0, cost 10.0,
    cost 0.0, cost 10.0, cost 10.0,
    cost 10.0, cost 10.0, cost 0.0]
  emit := {}
  unk := #[cost 0.0, cost 0.0, cost 0.0]

private def malformedHmm : Hmm :=
  { hmm with start := #[cost 0.0] }

private def compileTagger : Except NerTagger.CompileError NerTagger :=
  NerTagger.compile hmm #["x"] #["O", "B-X", "I-X"]

private def tokenOnly : Doc [.tokens] :=
  { text := "x x", spans := #[⟨0, 1⟩, ⟨2, 3⟩], forms := #["x", "x"] }

private def sentenced : Doc [.sents, .tokens] :=
  { tokenOnly with sentEnd := #[1, 2] }

private def oneToken : Doc [.tokens] :=
  { text := "x", spans := #[⟨0, 1⟩], forms := #["x"] }

private def emptyTokens : Doc [.tokens] :=
  { text := "" }

private def malformed : Doc [.sents, .tokens] :=
  { sentenced with spans := #[⟨0, 1⟩] }

example : tokenOnly.SemanticWF := by native_decide
example : sentenced.SemanticWF := by native_decide

private def pureSentenceAware : Bool :=
  match compileTagger with
  | .error _ => false
  | .ok tagger =>
      match tagger.tagDocument tokenOnly, tagger.tagDocument sentenced with
      | .ok whole, .ok split =>
          whole.ner == #["X", "O"] &&
            split.ner == #["X", "X"] &&
            decide whole.SemanticWF && decide split.SemanticWF &&
            NerTagger.documentWork split == 2
      | _, _ => false

#guard pureSentenceAware

private def testEffectful : IO Unit := do
  match ← NLP.runIO {} do
    let tagger ← NLP.compileNerTagger hmm #["x"] #["O", "B-X", "I-X"]
    NLP.tagNamedEntities tagger sentenced
  with
  | .ok (.ok output) =>
    if output.ner != #["X", "X"] || !decide output.SemanticWF then
      throw <| IO.userError "effectful NER ignored sentence boundaries or output alignment"
  | _ => throw <| IO.userError "valid NER input failed"

private def testLengthPolicy : IO Unit := do
  match ← NLP.runIO { maxLen := 1 } do
    let tagger ← NLP.compileNerTagger hmm #["x"] #["O", "B-X", "I-X"]
    NLP.tagNamedEntities tagger tokenOnly
  with
  | .ok (.skipped (.tooLong 2 1)) => pure ()
  | _ => throw <| IO.userError "NER length policy did not use the token-only sequence length"
  match ← NLP.runIO { maxLen := 1 } do
    let tagger ← NLP.compileNerTagger hmm #["x"] #["O", "B-X", "I-X"]
    NLP.tagNamedEntities tagger sentenced
  with
  | .ok (.ok output) =>
    if output.ner != #["X", "X"] then
      throw <| IO.userError "NER length policy did not operate per advertised sentence"
  | _ => throw <| IO.userError "valid one-token NER sentences were skipped"

private def testMalformedInput : IO Unit := do
  let .ok tagger := compileTagger
    | throw <| IO.userError "NER malformed-input fixture did not compile"
  match ← NLP.runIO {} <| NLP.tagNamedEntities tagger malformed with
  | .error (.invalidInput "NER tagger input" _) => pure ()
  | _ => throw <| IO.userError "malformed NER input crossed the semantic boundary"

private def testModelFailure : IO Unit := do
  match ← NLP.runIO {} <|
      NLP.compileNerTagger malformedHmm #["x"] #["O", "B-X", "I-X"] "models/ner.hmm" with
  | .error (.modelCorrupt "models/ner.hmm" why) =>
    if !why.contains "nTags=3, start=1, transitions=9, unknown=3" then
      throw <| IO.userError "NER model failure lost its constrained-HMM detail"
  | _ => throw <| IO.userError "invalid NER model crossed the checked model boundary"

private def testEstimate : IO Unit := do
  let training : Array (Array (String × String)) :=
    #[#[("x", "B-X")], #[("outside", "O")]]
  match ← NLP.runIO {} do
    let tagger ← NLP.estimateNerTagger training
    NLP.tagNamedEntities tagger oneToken
  with
  | .ok (.ok output) =>
    if output.ner.size != 1 || !decide output.SemanticWF then
      throw <| IO.userError "estimated NER tagger returned a misaligned document"
  | _ => throw <| IO.userError "valid NER training data failed"

private def testTrainingFailureSource : IO Unit := do
  match ← NLP.runIO {} <|
      NLP.estimateNerTagger #[#[("background", "B-O")]] 1.0 "training/entities.bio" with
  | .error (.modelCorrupt "training/entities.bio" why) =>
      unless why.contains "sentence 0, token 0" && why.contains "reserved" do
        throw <| IO.userError "NER training failure lost its source coordinates"
  | _ => throw <| IO.userError "reserved NER entity crossed the effectful model boundary"

private def testOrderedBatch : IO Unit := do
  let documents := #[oneToken, tokenOnly, emptyTokens, oneToken]
  let config : Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  let withMinimum ← NLP.runIO config do
    let tagger ← NLP.compileNerTagger hmm #["x"] #["O", "B-X", "I-X"]
    NLP.tagNamedEntitiesManyWithMinTokens 1 tagger documents
  let configured ← NLP.runIO config do
    let tagger ← NLP.compileNerTagger hmm #["x"] #["O", "B-X", "I-X"]
    NLP.tagNamedEntitiesMany tagger documents
  match withMinimum, configured with
  | .ok minimumOutput, .ok configuredOutput =>
    let labels := fun output ↦ output.map fun result ↦
      match result with
      | .ok doc => doc.ner
      | _ => #["unexpected"]
    let expected := #[#["X"], #["X", "O"], #[], #["X"]]
    if labels minimumOutput != expected || labels configuredOutput != expected then
      throw <| IO.userError "parallel NER lost stable order or an exact pure result"
  | .error cause, _ | _, .error cause =>
      throw <| IO.userError s!"parallel NER failed: {cause}"

private def testBatchFailureLocation : IO Unit := do
  let documents := #[sentenced, malformed]
  let config : Config := { numThreads := 2, parallelMinWeight := 1 }
  let withMinimum ← NLP.runIO config do
    let tagger ← NLP.compileNerTagger hmm #["x"] #["O", "B-X", "I-X"]
    NLP.tagNamedEntitiesManyWithMinTokens 1 tagger documents
  let configured ← NLP.runIO config do
    let tagger ← NLP.compileNerTagger hmm #["x"] #["O", "B-X", "I-X"]
    NLP.tagNamedEntitiesMany tagger documents
  match withMinimum, configured with
  | .error (.invalidInput "NER tagger input document 1" _),
      .error (.invalidInput "NER tagger input document 1" _) => pure ()
  | _, _ => throw <| IO.userError "parallel NER failure lost its document ordinal"

private def testCancelled : IO Unit := do
  let .ok tagger := compileTagger
    | throw <| IO.userError "NER cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.tagNamedEntities tagger oneToken)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "NER tagging lost its cancellation reason"

#eval testEffectful
#eval testLengthPolicy
#eval testMalformedInput
#eval testModelFailure
#eval testEstimate
#eval testTrainingFailureSource
#eval testOrderedBatch
#eval testBatchFailureLocation
#eval testCancelled

end NlpTests.Pipeline.Ner
