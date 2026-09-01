import Nlp.Pipeline.RegexNer

/-!
# Effectful RegexNER regression tests

These checks keep the pure model and preferred `NLP` facade aligned across sentence policy,
dynamic annotation requirements, ordered corpus traversal, diagnostics, and cancellation.
-/

namespace NlpTests.Pipeline.RegexNer

open Nlp Nlp.Pattern

/-- Mixed regular and exact-phrase fixture rules. -/
private def rules : Array RegexNerRule :=
  #[{ pattern := .regular (.atom (.form (.equal "Alice")))
      entityClass := "PERSON"
      priority := 1.0 },
    { pattern := .phrase #["New", "York"]
      entityClass := "LOCATION"
      priority := 2.0 }]

/-- Compile the shared pure fixture without erasing a typed failure. -/
private def model : Except RegexNerCompileError RegexNerModel :=
  RegexNerModel.compile rules

/-- Four checked tokens split into independent sentences of lengths three and one. -/
private def sentenced : Doc [.sents, .tokens] :=
  { text := "Alice New York Alice"
    spans := #[⟨0, 5⟩, ⟨6, 9⟩, ⟨10, 14⟩, ⟨15, 20⟩]
    forms := #["Alice", "New", "York", "Alice"]
    sentEnd := #[3, 4] }

/-- The same tokens interpreted as one sequence. -/
private def tokenOnly : Doc [.tokens] :=
  { sentenced with sentEnd := #[] }

/-- One-token fixture for ordered corpus traversal. -/
private def alice : Doc [.tokens] :=
  { text := "Alice", spans := #[⟨0, 5⟩], forms := #["Alice"] }

/-- Exact-phrase fixture for ordered corpus traversal. -/
private def newYork : Doc [.tokens] :=
  { text := "New York"
    spans := #[⟨0, 3⟩, ⟨4, 8⟩]
    forms := #["New", "York"] }

/-- Empty token documents remain checked and produce an empty class column. -/
private def empty : Doc [.tokens] :=
  { text := "" }

/-- A malformed document must fail before a matcher reads its columns. -/
private def malformed : Doc [.tokens] :=
  { text := "Alice", forms := #["Alice"] }

example : sentenced.SemanticWF := by native_decide
example : tokenOnly.SemanticWF := by native_decide
example : alice.SemanticWF := by native_decide
example : newYork.SemanticWF := by native_decide

/-- The effectful facade returns the exact pure checked result. -/
private def testEffectful : IO Unit := do
  let .ok expected := model
    | throw <| IO.userError "RegexNER fixture model did not compile"
  let .ok pureOutput := expected.tagDocument sentenced
    | throw <| IO.userError "pure RegexNER fixture failed"
  match ← NLP.runIO {} do
    let compiled ← NLP.compileRegexNerModel rules
    NLP.regexNer compiled sentenced
  with
  | .ok (.ok output) =>
      if output.ner != #["PERSON", "LOCATION", "LOCATION", "PERSON"] ||
          output.ner != pureOutput.ner || !decide output.SemanticWF then
        throw <| IO.userError "effectful RegexNER disagreed with its pure checked seam"
  | _ => throw <| IO.userError "valid effectful RegexNER input failed"

/-- Length policy is applied to advertised sentences rather than the flat token column. -/
private def testLengthPolicy : IO Unit := do
  let .ok compiled := model
    | throw <| IO.userError "RegexNER length-policy fixture did not compile"
  match ← NLP.runIO { maxLen := 3 } <| NLP.regexNer compiled tokenOnly with
  | .ok (.skipped (.tooLong 4 3)) => pure ()
  | _ => throw <| IO.userError "RegexNER did not bound the token-only sequence"
  match ← NLP.runIO { maxLen := 3 } <| NLP.regexNer compiled sentenced with
  | .ok (.ok output) =>
      if output.ner != #["PERSON", "LOCATION", "LOCATION", "PERSON"] then
        throw <| IO.userError "RegexNER did not treat advertised sentences independently"
  | _ => throw <| IO.userError "valid bounded RegexNER sentences were skipped"

/-- Missing dynamically required annotation columns are typed input failures. -/
private def testMissingLayer : IO Unit := do
  let posRules : Array RegexNerRule :=
    #[{ pattern := .regular (.atom (.pos (.equal "NNP")))
        entityClass := "PROPER" }]
  match ← NLP.runIO {} do
    let compiled ← NLP.compileRegexNerModel posRules
    NLP.regexNer compiled alice
  with
  | .error (.invalidInput "RegexNER input" why) =>
      unless why.contains "part of speech" do
        throw <| IO.userError "RegexNER missing-layer failure lost its field name"
  | _ => throw <| IO.userError "a missing RegexNER POS layer crossed validation"

/-- Model diagnostics retain the caller source and exact source-rule ordinal. -/
private def testCompileFailure : IO Unit := do
  let invalid : Array RegexNerRule :=
    #[{ pattern := .phrase #["Alice"], entityClass := "" }]
  match ← NLP.runIO {} <| NLP.compileRegexNerModel invalid "rules/people.regexner" with
  | .error (.modelCorrupt "rules/people.regexner" why) =>
      unless why.contains "rule 0" && why.contains "empty entity class" do
        throw <| IO.userError "RegexNER compile failure lost its stable coordinates"
  | _ => throw <| IO.userError "an invalid RegexNER rule crossed compilation"

/-- Pure range resource failures become explicit per-document skip reasons. -/
private def testRuntimeBudgets : IO Unit := do
  let regularRules : Array RegexNerRule :=
    #[{ pattern := .regular (.atom (.form .any)), entityClass := "TOKEN" }]
  match ← NLP.runIO {} do
    let compiled ← NLP.compileRegexNerModelWith { search := { maxWork := 0 } } regularRules
    NLP.regexNer compiled alice
  with
  | .ok (.skipped (.workLimit required 0)) =>
      unless 0 < required do
        throw <| IO.userError "RegexNER work skip lost its conservative requirement"
  | _ => throw <| IO.userError "RegexNER work budget did not become a skip reason"
  let phraseRules : Array RegexNerRule :=
    #[{ pattern := .phrase #["Alice"], entityClass := "PERSON" }]
  match ← NLP.runIO {} do
    let compiled ←
      NLP.compileRegexNerModelWith { search := { maxMatches := 0 } } phraseRules
    NLP.regexNer compiled alice
  with
  | .ok (.skipped (.candidateLimit 1 0)) => pure ()
  | _ => throw <| IO.userError "RegexNER candidate budget did not become a skip reason"

/-- Semantic failures retain the corpus ordinal selected by stable traversal. -/
private def testBatchFailureLocation : IO Unit := do
  let .ok compiled := model
    | throw <| IO.userError "RegexNER batch-failure fixture did not compile"
  match ← NLP.runIO { numThreads := 2, parallelMinWeight := 1 } <|
      NLP.regexNerManyWithMinTokens 1 compiled #[alice, malformed] with
  | .error (.invalidInput "RegexNER input document 1" _) => pure ()
  | _ => throw <| IO.userError "parallel RegexNER failure lost its document ordinal"

/-- Token-weighted parallel execution preserves exact input order. -/
private def testOrderedBatch : IO Unit := do
  let .ok compiled := model
    | throw <| IO.userError "RegexNER ordered-batch fixture did not compile"
  let documents := #[alice, newYork, empty, alice]
  let config : Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config <| NLP.regexNerManyWithMinTokens 1 compiled documents with
  | .ok output =>
      let classes := output.map fun result ↦
        match result with
        | .ok doc => doc.ner
        | _ => #["unexpected"]
      if classes != #[#["PERSON"], #["LOCATION", "LOCATION"], #[], #["PERSON"]] then
        throw <| IO.userError "parallel RegexNER lost stable order or an exact result"
  | .error cause => throw <| IO.userError s!"parallel RegexNER failed: {cause}"

/-- A cancelled environment is observed before document validation or matching. -/
private def testCancelled : IO Unit := do
  let .ok compiled := model
    | throw <| IO.userError "RegexNER cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.regexNer compiled alice)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "RegexNER lost its cancellation reason"

#eval testEffectful
#eval testLengthPolicy
#eval testMissingLayer
#eval testCompileFailure
#eval testRuntimeBudgets
#eval testBatchFailureLocation
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.RegexNer
