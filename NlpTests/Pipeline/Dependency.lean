import Nlp.Pipeline.Dependency

/-! Functional and effectful projective dependency pipeline regression tests. -/

namespace NlpTests.Pipeline.Dependency

open Nlp Nlp.Dependency

private def scorer (sentence : Sentence) (head dependent relation : Nat) : Float :=
  if head = 0 then
    if sentence.pos? dependent == some "VERB" then 0.0 else 20.0
  else if relation = 1 then
    if sentence.pos? head == some "VERB" then 1.0 else 5.0
  else
    8.0

private def parser : Except ArcScoreError Parser :=
  Parser.compile #["root", "dep"] 0 scorer

private def sentence : Doc [.pos, .sents, .tokens] :=
  { text := "dogs run fast", spans := #[⟨0, 4⟩, ⟨5, 8⟩, ⟨9, 13⟩],
    forms := #["dogs", "run", "fast"], sentEnd := #[3],
    pos := #["NOUN", "VERB", "ADV"] }

private def twoSentences : Doc [.pos, .sents, .tokens] :=
  { text := "dogs run cats sleep",
    spans := #[⟨0, 4⟩, ⟨5, 8⟩, ⟨9, 13⟩, ⟨14, 19⟩],
    forms := #["dogs", "run", "cats", "sleep"], sentEnd := #[2, 4],
    pos := #["NOUN", "VERB", "NOUN", "VERB"] }

private def pureDocument : Bool :=
  match parser with
  | .error _ => false
  | .ok model =>
      match model.parseDocument? twoSentences with
      | .ok (some output) =>
          output.head == #[2, 0, 2, 0] &&
            output.deprel == #["dep", "root", "dep", "root"] &&
            decide output.SemanticWF && Parser.documentWork twoSentences == 16
      | _ => false

#guard pureDocument

def testEffectful : IO Unit := do
  match ← NLP.runIO {} do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 scorer
    NLP.parseDependencies model sentence
  with
  | .ok (.ok output) =>
      if output.head != #[2, 0, 2] || output.deprel != #["dep", "root", "dep"] ||
          !decide output.SemanticWF then
        throw <| IO.userError "effectful dependency parse changed its exact tree"
  | _ => throw <| IO.userError "valid dependency document did not parse"

def testPoliciesAndNoAnalysis : IO Unit := do
  match ← NLP.runIO { maxLen := 2 } do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 scorer
    NLP.parseDependencies model sentence
  with
  | .ok (.skipped (.tooLong 3 2)) => pure ()
  | _ => throw <| IO.userError "dependency length policy did not run before inference"
  match ← NLP.runIO { maxChartEntries := 23 } do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 scorer
    NLP.parseDependencies model sentence
  with
  | .ok (.skipped (.chartTooLarge 24 23)) => pure ()
  | _ => throw <| IO.userError "dependency chart policy did not run before allocation"
  match ← NLP.runIO {} do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 fun _ _ _ _ => inf
    NLP.parseDependencies model sentence
  with
  | .ok .noAnalysis => pure ()
  | _ => throw <| IO.userError "forbidden dependency system did not return no-analysis"

private def malformed : Doc [.pos, .sents, .tokens] :=
  { sentence with spans := #[⟨0, 4⟩] }

def testInvalidInputAndScore : IO Unit := do
  let .ok model := parser
    | throw <| IO.userError "dependency fixture parser did not compile"
  match ← NLP.runIO {} <| NLP.parseDependencies model malformed with
  | .error (.invalidInput "dependency parser input" _) => pure ()
  | _ => throw <| IO.userError "malformed dependency input crossed the checked boundary"
  let bad : Scorer := fun _ head dependent relation =>
    if head = 0 && dependent = 1 && relation = 0 then -1.0 else 0.0
  match ← NLP.runIO {} do
    let badModel ← NLP.compileDependencyParser #["root", "dep"] 0 bad "models/dep"
    NLP.parseDependencies badModel sentence
  with
  | .error (.modelCorrupt "models/dep" why) =>
      if !why.contains "head=0 dependent=1 relation=0" then
        throw <| IO.userError "dynamic dependency failure lost its arc coordinates"
  | _ => throw <| IO.userError "invalid dynamic dependency score was accepted"

def testOrderedBatch : IO Unit := do
  let documents := #[sentence, sentence, sentence]
  let config : Config := {
    numThreads := 3
    parallelMinWeight := 1
    maxDedicatedThreads := 3
  }
  match ← NLP.runIO config do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 scorer
    NLP.parseDependenciesManyWithMinWork 1 model documents
  with
  | .ok output =>
    if output.size != 3 || !output.all (fun result =>
        match result with
        | .ok doc => doc.head == #[2, 0, 2]
        | _ => false) then
      throw <| IO.userError "dependency batch lost order or an exact tree"
  | .error cause => throw <| IO.userError s!"dependency batch failed: {cause}"

def testCancelled : IO Unit := do
  let .ok model := parser
    | throw <| IO.userError "dependency cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.parseDependencies model sentence)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "dependency parsing lost its cancellation reason"

#eval testEffectful
#eval testPoliciesAndNoAnalysis
#eval testInvalidInputAndScore
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.Dependency
