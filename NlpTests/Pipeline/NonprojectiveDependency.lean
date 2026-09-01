import Nlp.Pipeline.NonprojectiveDependency

/-! Functional and effectful single-root nonprojective dependency pipeline regression tests. -/

namespace NlpTests.Pipeline.NonprojectiveDependency

open Nlp Nlp.Dependency

/-- A scorer whose unique zero-cost tree contains two crossing arcs. -/
private def crossingScorer (_sentence : Sentence) (head dependent relation : Nat) : Float :=
  if head = 0 then
    if dependent = 3 then 0.0 else 20.0
  else if relation = 1 then
    if (head = 3 && dependent = 1) || (head = 4 && dependent = 2) ||
        (head = 3 && dependent = 4) then
      0.0
    else
      20.0
  else
    40.0

/-- Reusable caller-scored parser shared by the projective and nonprojective lanes. -/
private def parser : Except ArcScoreError Parser :=
  Parser.compile #["root", "dep"] 0 crossingScorer

/-- Four-token document whose nonprojective optimum is uniquely determined. -/
private def sentence : Doc [.pos, .sents, .tokens] :=
  { text := "one two three four",
    spans := #[⟨0, 3⟩, ⟨4, 7⟩, ⟨8, 13⟩, ⟨14, 18⟩],
    forms := #["one", "two", "three", "four"],
    sentEnd := #[4],
    pos := #["NOUN", "NOUN", "VERB", "NOUN"] }

/-- A one-token document makes batch order observable by output length. -/
private def singleton : Doc [.pos, .sents, .tokens] :=
  { text := "one", spans := #[⟨0, 3⟩], forms := #["one"], sentEnd := #[1], pos := #["NOUN"] }

/-- A valid two-token input whose only tree has an unreportable aggregate Float cost. -/
private def overflowSentence : Doc [.pos, .sents, .tokens] :=
  { text := "one two",
    spans := #[⟨0, 3⟩, ⟨4, 7⟩],
    forms := #["one", "two"],
    sentEnd := #[2],
    pos := #["NOUN", "NOUN"] }

/-- Every source arc is finite, but the only complete analysis overflows operational Float. -/
private def overflowScorer (_sentence : Sentence) (head dependent relation : Nat) : Float :=
  if head = 0 && dependent = 1 then
    1.0e308
  else if relation = 1 && head = 1 && dependent = 2 then
    1.0e308
  else
    inf

/-- Functional document decoding returns the exact crossing tree with checked semantics. -/
private def pureDocument : Bool :=
  match parser with
  | .error _ => false
  | .ok model =>
      match model.parseNonprojectiveDocument? sentence with
      | .ok (some output) =>
          output.head == #[3, 4, 0, 3] &&
            output.deprel == #["dep", "dep", "root", "dep"] &&
            decide output.SemanticWF &&
            Parser.nonprojectiveDocumentWork sentence == 16 &&
            match checkProjective output.head with
            | .error (.crossing 1 3 2 4) => true
            | _ => false
      | _ => false

#guard pureDocument

/-- The added lane does not change the original project's projectivity guarantee. -/
private def existingProjectiveLaneRemainsProjective : Bool :=
  match parser with
  | .error _ => false
  | .ok model =>
      match model.parseDocument? sentence with
      | .ok (some output) => (checkProjective output.head).isOk
      | _ => false

#guard existingProjectiveLaneRemainsProjective

/-- Full-column functional decoding uses the same sentence-local coordinates and labels. -/
private def pureArrays : Bool :=
  match parser with
  | .error _ => false
  | .ok model =>
      match model.parseNonprojectiveArrays? sentence.forms sentence.pos with
      | .ok (some result) =>
          result.heads == #[3, 4, 0, 3] &&
            result.relations == #["dep", "dep", "root", "dep"]
      | _ => false

#guard pureArrays

/-- The effectful facade returns the same exact nonprojective document. -/
def testEffectful : IO Unit := do
  match ← NLP.runIO {} do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 crossingScorer
    NLP.parseNonprojectiveDependencies model sentence
  with
  | .ok (.ok output) =>
      if output.head != #[3, 4, 0, 3] ||
          output.deprel != #["dep", "dep", "root", "dep"] ||
          !decide output.SemanticWF then
        throw <| IO.userError "effectful nonprojective dependency parse changed its exact tree"
  | _ => throw <| IO.userError "valid nonprojective dependency document did not parse"

/-- Runtime length and exact workspace limits run before the pure decoder. -/
def testPoliciesAndNoAnalysis : IO Unit := do
  match ← NLP.runIO { maxLen := 3 } do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 crossingScorer
    NLP.parseNonprojectiveDependencies model sentence
  with
  | .ok (.skipped (.tooLong 4 3)) => pure ()
  | _ => throw <| IO.userError "nonprojective length policy did not run before inference"
  let required := Arborescence.workspaceEntryCount 4
  match ← NLP.runIO { maxChartEntries := required } do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 crossingScorer
    NLP.parseNonprojectiveDependencies model sentence
  with
  | .ok (.ok output) =>
      if output.head != #[3, 4, 0, 3] then
        throw <| IO.userError "exact nonprojective workspace limit changed the decoded tree"
  | _ => throw <| IO.userError "exact nonprojective workspace limit was rejected"
  match ← NLP.runIO { maxChartEntries := required - 1 } do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 crossingScorer
    NLP.parseNonprojectiveDependencies model sentence
  with
  | .ok (.skipped (.chartTooLarge found limit)) =>
      if found != required || limit != required - 1 then
        throw <| IO.userError "nonprojective workspace policy lost its exact dimensions"
  | _ => throw <| IO.userError "nonprojective workspace policy did not run before allocation"
  match ← NLP.runIO {} do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 fun _ _ _ _ => inf
    NLP.parseNonprojectiveDependencies model sentence
  with
  | .ok .noAnalysis => pure ()
  | _ => throw <| IO.userError "forbidden nonprojective system did not return no-analysis"
  match ← NLP.runIO {} do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 overflowScorer
    NLP.parseNonprojectiveDependencies model overflowSentence
  with
  | .ok (.ok output) =>
      if output.head != #[0, 1] || output.deprel != #["root", "dep"] then
        throw <| IO.userError "exact overflow analysis changed its selected tree"
  | _ => throw <| IO.userError "exact overflow analysis was discarded by the effectful API"

/-- Invalid inputs and dynamic score failures retain typed source diagnostics. -/
def testInvalidInputAndScore : IO Unit := do
  let .ok model := parser
    | throw <| IO.userError "nonprojective dependency fixture parser did not compile"
  let malformed : Doc [.pos, .sents, .tokens] := { sentence with spans := #[⟨0, 3⟩] }
  match ← NLP.runIO {} <| NLP.parseNonprojectiveDependencies model malformed with
  | .error (.invalidInput "nonprojective dependency parser input" _) => pure ()
  | _ => throw <| IO.userError "malformed input crossed the nonprojective checked boundary"
  let bad : Scorer := fun _ head dependent relation =>
    if head = 0 && dependent = 1 && relation = 0 then -1.0 else 0.0
  match ← NLP.runIO {} do
    let badModel ← NLP.compileDependencyParser #["root", "dep"] 0 bad "models/nonproj"
    NLP.parseNonprojectiveDependencies badModel sentence
  with
  | .error (.modelCorrupt "models/nonproj" why) =>
      if !why.contains "sentence 0 tokens [0, 4)" ||
          !why.contains "head=0 dependent=1 relation=0" then
        throw <| IO.userError "nonprojective score failure lost its source coordinates"
  | _ => throw <| IO.userError "invalid nonprojective dynamic score was accepted"

/-- Quadratic-weighted concurrency preserves document order and every exact tree. -/
def testOrderedBatch : IO Unit := do
  let documents := #[sentence, singleton, sentence]
  let config : Config := {
    numThreads := 3
    parallelMinWeight := 1
    maxDedicatedThreads := 3
  }
  match ← NLP.runIO config do
    let model ← NLP.compileDependencyParser #["root", "dep"] 0 crossingScorer
    NLP.parseNonprojectiveDependenciesManyWithMinWork 1 model documents
  with
  | .ok output =>
      let exact := output.size == 3 &&
        match output[0]?, output[1]?, output[2]? with
        | some (Analysis.ok first), some (Analysis.ok second),
            some (Analysis.ok third) =>
            first.head == #[3, 4, 0, 3] && second.head == #[0] &&
              third.head == #[3, 4, 0, 3]
        | _, _, _ => false
      unless exact do
        throw <| IO.userError "nonprojective dependency batch lost order or an exact tree"
  | .error cause => throw <| IO.userError s!"nonprojective dependency batch failed: {cause}"

/-- Cancellation is observed before any nonprojective sentence kernel starts. -/
def testCancelled : IO Unit := do
  let .ok model := parser
    | throw <| IO.userError "nonprojective cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <|
      (NLP.runIn env (NLP.parseNonprojectiveDependencies model sentence)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "nonprojective parsing lost its cancellation reason"

#eval testEffectful
#eval testPoliciesAndNoAnalysis
#eval testInvalidInputAndScore
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.NonprojectiveDependency
