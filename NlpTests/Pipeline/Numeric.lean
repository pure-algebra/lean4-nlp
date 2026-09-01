import Nlp.Pipeline.Numeric

/-! Functional/effectful exact numeric-normalization boundary tests. -/

namespace NlpTests.Pipeline.Numeric

open Nlp Nlp.Normalize

/-- Two exact expressions separated by a nonnumeric token. -/
private def source : Doc [.sents, .tokens] :=
  { text := "one hundred cats 21st"
    spans := #[⟨0, 3⟩, ⟨4, 11⟩, ⟨12, 16⟩, ⟨17, 21⟩]
    forms := #["one", "hundred", "cats", "21st"]
    sentEnd := #[4] }

/-- A one-token document makes batch ordering observable. -/
private def singleton : Doc [.sents, .tokens] :=
  { text := "seven"
    spans := #[⟨0, 5⟩]
    forms := #["seven"]
    sentEnd := #[1] }

private def literalSource : Doc [.sents, .tokens] :=
  { text := "123"
    spans := #[⟨0, 3⟩]
    forms := #["123"]
    sentEnd := #[1] }

private def scaledSource : Doc [.sents, .tokens] :=
  { text := "nine trillion"
    spans := #[⟨0, 4⟩, ⟨5, 13⟩]
    forms := #["nine", "trillion"]
    sentEnd := #[2] }

private def malformedLiteral : Doc [.sents, .tokens] :=
  { text := "1e"
    spans := #[⟨0, 2⟩]
    forms := #["1e"]
    sentEnd := #[1] }

private def singletonSentenceCount : Nat :=
  256

private def singletonSentences : Doc [.sents, .tokens] :=
  { text := String.ofList (List.replicate singletonSentenceCount 'x')
    spans := (Array.range singletonSentenceCount).map fun index ↦ ⟨index, index + 1⟩
    forms := Array.replicate singletonSentenceCount "one"
    sentEnd := (Array.range singletonSentenceCount).map fun index ↦ index + 1 }

#guard decide source.SemanticWF
#guard decide singletonSentences.SemanticWF
#guard Numeric.documentWork source == 22

/- The functional boundary emits exact values and proof-carrying full-column spans. -/
#guard
  match Numeric.normalizeDocument source with
  | .error _ => false
  | .ok result =>
      result.source == source.forms && result.ranges == #[(0, 4)] && result.size == 2 &&
        match result.mentions[0]?, result.mentions[1]? with
        | some first, some second =>
            first.start == 0 && first.stop == 2 && first.kind == .cardinal &&
              first.value.rational == mkRat 100 1 &&
            second.start == 3 && second.stop == 4 && second.kind == .ordinal &&
              second.value.rational == mkRat 21 1
        | _, _ => false

/-- The preferred effectful facade returns the exact functional result. -/
def testEffectParity : IO Unit := do
  let .ok expected := Numeric.normalizeDocument source
    | throw <| IO.userError "numeric fixture failed at the functional boundary"
  match ← NLP.runIO {} <| NLP.normalizeNumbers source with
  | .ok (.ok actual) =>
      unless actual == expected do
        throw <| IO.userError "effectful numeric normalization diverged from the pure API"
  | _ => throw <| IO.userError "valid numeric input was not analyzed"

/-- Runtime length and exact kernel limits become typed non-results. -/
def testLimits : IO Unit := do
  match ← NLP.runIO { maxLen := 3 } <| NLP.normalizeNumbers source with
  | .ok (.skipped (.tooLong 4 3)) => pure ()
  | _ => throw <| IO.userError "numeric normalization ignored runtime maxLen"
  match ← NLP.runIO {} <|
      NLP.normalizeNumbersWith { maxCandidates := 0 } source with
  | .ok (.skipped (.candidateLimit 1 0)) => pure ()
  | _ => throw <| IO.userError "numeric candidate limit lost its exact first unit"
  let required ←
    match Numeric.normalizeDocumentWith { maxWork := 0 } source with
    | .error (.workBudget required 0) => pure required
    | _ => throw <| IO.userError "pure numeric work limit accepted a nonempty document"
  match ← NLP.runIO {} <| NLP.normalizeNumbersWith { maxWork := 0 } source with
  | .ok (.skipped (.workLimit found 0)) =>
      unless found == required do
        throw <| IO.userError "effectful numeric work limit changed the required count"
  | _ => throw <| IO.userError "numeric work limit did not become a typed skip"
  match ← NLP.runIO {} <|
      NLP.normalizeNumbersWith { maxBytesPerMention := 2 } literalSource with
  | .ok (.skipped (.byteLimit 3 2)) => pure ()
  | _ => throw <| IO.userError "literal byte limit did not become a typed skip"
  match ← NLP.runIO {} <| NLP.normalizeNumbersWith { maxDigits := 2 } literalSource with
  | .ok (.skipped (.workLimit 3 2)) => pure ()
  | _ => throw <| IO.userError "literal digit limit did not become a typed skip"
  match ← NLP.runIO {} <|
      NLP.normalizeNumbersWith { maxValueDigits := 2 } literalSource with
  | .ok (.skipped (.workLimit 3 2)) => pure ()
  | _ => throw <| IO.userError "literal value limit did not become a typed skip"
  match ← NLP.runIO {} <|
      NLP.normalizeNumbersWith { maxValueDigits := 13 } scaledSource with
  | .ok (.ok result) =>
      match result.mentions with
      | #[mention] =>
          unless mention.value.rational == mkRat 9_000_000_000_000 1 do
            throw <| IO.userError "exact English value limit changed the result"
      | _ => throw <| IO.userError "exact English value limit lost its mention"
  | _ => throw <| IO.userError "exact English value limit unexpectedly skipped"
  match ← NLP.runIO {} <|
      NLP.normalizeNumbersWith { maxValueDigits := 12 } scaledSource with
  | .ok (.skipped (.workLimit 13 12)) => pure ()
  | _ => throw <| IO.userError "one-short English value limit was not a typed skip"

/-- Semantic input failures remain outer effect failures with a stable location. -/
def testInvalidInput : IO Unit := do
  let malformed : Doc [.sents, .tokens] := { source with spans := #[⟨0, 3⟩] }
  match ← NLP.runIO {} <| NLP.normalizeNumbers malformed with
  | .error (.invalidInput location why) =>
      unless location == "numeric normalization input" && why.contains "semantic validation" do
        throw <| IO.userError "numeric invalid-input diagnostics lost their boundary"
  | _ => throw <| IO.userError "malformed numeric input crossed semantic validation"
  match ← NLP.runIO {} <| NLP.normalizeNumbers malformedLiteral with
  | .error (.invalidInput location why) =>
      unless location == "numeric normalization token 0" && why.contains "invalidSyntax" do
        throw <| IO.userError "malformed literal lost its absolute token diagnostic"
  | _ => throw <| IO.userError "malformed literal became a resource skip"

/-- Length policy precedes range work; exact range work precedes allocation and kernel errors. -/
def testRangePreflightPrecedence : IO Unit := do
  match ← NLP.runIO { maxLen := 0 } <|
      NLP.normalizeNumbersWith { maxWork := 255 } singletonSentences with
  | .ok (.skipped (.tooLong 1 0)) => pure ()
  | _ => throw <| IO.userError "numeric maxLen lost precedence over range work"
  match ← NLP.runIO { maxLen := 1 } <|
      NLP.normalizeNumbersWith { maxWork := 255 } singletonSentences with
  | .ok (.skipped (.workLimit 256 255)) => pure ()
  | _ => throw <| IO.userError "numeric range work was not rejected before allocation"
  match ← NLP.runIO { maxLen := 1 } <|
      NLP.normalizeNumbersWith { maxWork := 256 } singletonSentences with
  | .ok (.skipped (.workLimit 288 256)) => pure ()
  | _ => throw <| IO.userError "numeric checked core double-charged its range baseline"
  match ← NLP.runIO {} <|
      NLP.normalizeNumbersWith { maxWork := 0 } malformedLiteral with
  | .ok (.skipped (.workLimit 1 0)) => pure ()
  | _ => throw <| IO.userError "numeric kernel input error crossed the range-work fence"

/-- Work-weighted parallel batches preserve stable document order. -/
def testOrderedBatch : IO Unit := do
  let documents := #[source, singleton, source]
  let runtime : Nlp.Config :=
    { numThreads := 3, parallelMinWeight := 1, maxDedicatedThreads := 3 }
  match ← NLP.runIO runtime <| NLP.normalizeNumbersManyWithMinWork 1 {} documents with
  | .error cause => throw <| IO.userError s!"numeric batch failed: {cause}"
  | .ok output =>
      unless output.size == 3 do
        throw <| IO.userError "numeric batch changed the document count"
      match output[0]?, output[1]?, output[2]? with
      | some (Analysis.ok first), some (Analysis.ok second),
          some (Analysis.ok third) =>
          unless first.source.size == 4 && second.source.size == 1 &&
              third.source.size == 4 do
            throw <| IO.userError "numeric batch changed stable input order"
      | _, _, _ => throw <| IO.userError "numeric batch did not analyze every document"
  let shortRuntime := { runtime with maxLen := 1 }
  match ← NLP.runIO shortRuntime <|
      NLP.normalizeNumbersManyWithMinWork 1 {} documents with
  | .ok #[.skipped (.tooLong 4 1), .ok _, .skipped (.tooLong 4 1)] => pure ()
  | _ => throw <| IO.userError "numeric mixed batch changed stable input order"

/-- Cancellation is observed before semantic validation or exact-number allocation. -/
def testCancelled : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.normalizeNumbers source)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "numeric cancellation reason was lost"
  match ← liftM <|
      (NLP.runIn env (NLP.normalizeNumbersWith { maxWork := 0 } malformedLiteral)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "numeric budget/input errors outranked cancellation"

#eval testEffectParity
#eval testLimits
#eval testInvalidInput
#eval testRangePreflightPrecedence
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.Numeric
