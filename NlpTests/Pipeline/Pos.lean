import Nlp.Pipeline.Pos

namespace NlpTests.Pipeline.Pos

open Nlp Nlp.Sequence

private def cost (value : Float) : Cost := ⟨value⟩

private def hmm : Hmm where
  nTags := 2
  start := #[cost 0.0, cost 10.0]
  trans := #[cost 5.0, cost 0.0, cost 5.0, cost 0.0]
  emit := {}
  unk := #[cost 0.0, cost 0.0]

private def malformedHmm : Hmm :=
  { hmm with start := #[cost 0.0] }

private def compileTagger : Except PosTagger.CompileError PosTagger :=
  PosTagger.compile hmm #["x"] #["A", "B"]

private def tokenOnly : Doc [.tokens] :=
  { text := "x x", spans := #[⟨0, 1⟩, ⟨2, 3⟩], forms := #["x", "x"] }

private def sentenced : Doc [.sents, .tokens] :=
  { tokenOnly with sentEnd := #[1, 2] }

private def malformed : Doc [.tokens] :=
  { tokenOnly with spans := #[⟨0, 1⟩] }

example : tokenOnly.SemanticWF := by native_decide
example : sentenced.SemanticWF := by native_decide

example (tagger : PosTagger) : (tagger.tagDoc sentenced).WF :=
  tagger.tagDoc_wf sentenced (by native_decide)

example (tagger : PosTagger) : (tagger.tagDoc sentenced).SemanticWF :=
  tagger.tagDoc_semanticWF sentenced (by native_decide)

private def sentenceAware : Bool :=
  match compileTagger with
  | .ok tagger =>
      tagger.tagForms tokenOnly.forms == #["A", "B"] &&
        (tagger.tagDoc tokenOnly).pos == #["A", "B"] &&
        (tagger.tagDoc sentenced).pos == #["A", "A"] &&
        (tagger.annotator.run (by decide) sentenced).pos == #["A", "A"]
  | .error _ => false

#guard sentenceAware

private def malformedSentenceEndsFallBack : Bool :=
  match compileTagger with
  | .ok tagger =>
      let forms := #["x", "x", "x"]
      let malformedEnds := #[2, 1, 2]
      !PosTagger.sentenceEndsValid forms.size malformedEnds &&
        tagger.tagFormsWithSentences forms malformedEnds == tagger.tagForms forms
  | .error _ => false

#guard malformedSentenceEndsFallBack

private def testSingle : IO Unit := do
  match ← NLP.runIO {} do
    let tagger ← NLP.compilePosTagger hmm #["x"] #["A", "B"]
    NLP.tag tagger sentenced
  with
  | .ok output =>
    if output.pos != #["A", "A"] || output.text != sentenced.text then
      throw <| IO.userError "effectful POS tagging ignored sentence boundaries"
  | .error cause => throw <| IO.userError s!"valid POS input failed: {cause}"

private def testMalformed : IO Unit := do
  match ← NLP.runIO {} do
    let tagger ← NLP.compilePosTagger hmm #["x"] #["A", "B"]
    NLP.tag tagger malformed
  with
  | .error (.invalidInput "POS tagger input" _) => pure ()
  | _ => throw <| IO.userError "malformed POS input crossed the checked boundary"

private def testModelFailure : IO Unit := do
  match ← NLP.runIO {} <|
      NLP.compilePosTagger malformedHmm #["x"] #["A", "B"] "models/pos.hmm" with
  | .error (.modelCorrupt "models/pos.hmm" why) =>
    let expected :=
      "HMM dimensions disagree: nTags=2, start=1, transitions=4, unknown=2; " ++
        "expected nTags, nTags*nTags, nTags"
    if why != expected then
      throw <| IO.userError "POS model failure lost its actionable detail"
  | _ => throw <| IO.userError "invalid POS model crossed the checked model boundary"

private def testEstimate : IO Unit := do
  let training : Array (Array (String × String)) :=
    #[#[("x", "A")], #[("x", "A")]]
  match ← NLP.runIO {} do
    let tagger ← NLP.estimatePosTagger training
    NLP.tag tagger tokenOnly
  with
  | .ok output =>
    if output.pos != #["A", "A"] then
      throw <| IO.userError "effectful POS estimation did not produce its observed tag"
  | .error cause => throw <| IO.userError s!"valid POS training data failed: {cause}"

private def oneToken : Doc [.tokens] :=
  { text := "x", spans := #[⟨0, 1⟩], forms := #["x"] }

private def emptyTokens : Doc [.tokens] :=
  { text := "" }

private def testOrderedBatch : IO Unit := do
  let documents := #[oneToken, tokenOnly, oneToken, emptyTokens]
  let config : Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config do
    let tagger ← NLP.compilePosTagger hmm #["x"] #["A", "B"]
    NLP.tagManyWithMinTokens 1 tagger documents
  with
  | .ok output =>
    if output.map (fun doc ↦ doc.pos) != #[#["A"], #["A", "B"], #["A"], #[]] then
      throw <| IO.userError "parallel POS tagging lost input order or a pure result"
  | .error cause => throw <| IO.userError s!"parallel POS tagging failed: {cause}"

private def testCancelled : IO Unit := do
  let .ok tagger := compileTagger
    | throw <| IO.userError "POS cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.tag tagger oneToken)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "POS tagging lost its cancellation reason"

#eval testSingle
#eval testMalformed
#eval testModelFailure
#eval testEstimate
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.Pos
