import Nlp.Pipeline.EnhancedDependency

/-! Functional and effectful enhanced-dependency document regression tests. -/

namespace NlpTests.Pipeline.EnhancedDependency

open Nlp Nlp.Dependency

/-- Two checked basic-dependency sentences with a lexicalized marker in the second. -/
private def multiSentence : Doc [.dep, .lemma, .pos, .sents, .tokens] :=
  { text := "Dogs run Cats in boxes"
    spans := #[⟨0, 4⟩, ⟨5, 8⟩, ⟨9, 13⟩, ⟨14, 16⟩, ⟨17, 22⟩]
    forms := #["Dogs", "run", "Cats", "in", "boxes"]
    sentEnd := #[2, 5]
    pos := #["NOUN", "VERB", "NOUN", "ADP", "NOUN"]
    lemma := #["dog", "run", "cat", "in", "box"]
    head := #[2, 0, 0, 3, 1]
    deprel := #["nsubj", "root", "root", "case", "nmod"] }

/-- A one-token checked document makes token-weighted batch order observable. -/
private def singleton : Doc [.dep, .lemma, .pos, .sents, .tokens] :=
  { text := "Solo"
    spans := #[⟨0, 4⟩]
    forms := #["Solo"]
    sentEnd := #[1]
    pos := #["NOUN"]
    lemma := #["solo"]
    head := #[0]
    deprel := #["root"] }

/-- A compact computational signature for proof-irrelevant document-result comparison. -/
private def resultShape (result : EnglishEnhanced.Result) :=
  (result.graph.nodes, result.graph.offsets, result.graph.heads,
    result.graph.relations, result.graph.origins, result.counts.basic,
    result.counts.lexicalized, result.counts.propagated)

/-- Compare two enhanced documents without comparing their erased proof fields. -/
private def sameOutput (left right : EnglishEnhanced.Document available) : Bool :=
  left.source.forms == right.source.forms && left.ranges == right.ranges &&
    left.results.map resultShape == right.results.map resultShape

/- The source fixture satisfies the full advertised semantic boundary. -/
#guard decide multiSentence.SemanticWF

/- Pure document enhancement retains exact ranges and resets graph nodes per sentence. -/
#guard match EnglishEnhanced.enhanceDocument? multiSentence with
  | .error _ => false
  | .ok document =>
    document.source.forms == multiSentence.forms &&
      document.ranges == #[(0, 2), (2, 5)] && document.sentenceCount == 2 &&
      match document.results[0]?, document.results[1]? with
      | some first, some second =>
          first.graph.nodes == #[.word 1, .word 2] && first.graph.edgeCount == 2 &&
            second.graph.nodes == #[.word 1, .word 2, .word 3] &&
            second.graph.heads == #[.root, .word 3, .word 1, .word 1] &&
            second.graph.relations == #["root", "case", "nmod", "nmod:in"] &&
            decide (second.counts = ⟨3, 1, 0⟩)
      | _, _ => false

/-- Public alignment proofs compose to the exact source sentence count. -/
example (document : EnglishEnhanced.Document available) :
    document.results.size = document.source.sentenceRanges.size := by
  rw [document.resultCount_eq, document.ranges_eq]

/- Exact pure candidate and edge limits accept equality. -/
#guard
  let exact : EnglishEnhanced.Config := { maxCandidates := 1, maxEdges := 4 }
  (EnglishEnhanced.enhanceDocumentWith? exact multiSentence).isOk

/- A one-short candidate limit retains the second sentence and source range. -/
#guard
  let short : EnglishEnhanced.Config := { maxCandidates := 0, maxEdges := 4 }
  match EnglishEnhanced.enhanceDocumentWith? short multiSentence with
  | .error (.sentence 1 2 5 (.candidateBudget 1 0)) => true
  | _ => false

/- A one-short edge limit retains the exact total needed by the second sentence. -/
#guard
  let short : EnglishEnhanced.Config := { maxCandidates := 1, maxEdges := 3 }
  match EnglishEnhanced.enhanceDocumentWith? short multiSentence with
  | .error (.sentence 1 2 5 (.edgeBudget 4 3)) => true
  | _ => false

/- Pure malformed input is rejected at the single semantic validation boundary. -/
#guard
  let malformed : Doc [.dep, .lemma, .pos, .sents, .tokens] :=
    { multiSentence with lemma := #["dog"] }
  match EnglishEnhanced.enhanceDocument? malformed with
  | .error (.input (.structural _)) => true
  | _ => false

/-- The preferred effectful facade returns the exact pure functional result. -/
def testEffectParity : IO Unit := do
  let .ok expected := EnglishEnhanced.enhanceDocument? multiSentence
    | throw <| IO.userError "pure enhanced-dependency document fixture failed"
  match ← NLP.runIO {} <| NLP.enhanceDependencies multiSentence with
  | .ok (.ok actual) =>
      unless sameOutput expected actual do
        throw <| IO.userError "effectful enhancement diverged from the pure document API"
  | _ => throw <| IO.userError "valid enhanced-dependency document was not analysed"

/-- Runtime clamps preserve exact equality and map one-short limits to typed skips. -/
def testRuntimeLimits : IO Unit := do
  match ← NLP.runIO { maxGraphCandidates := 1, maxGraphEdges := 4 } <|
      NLP.enhanceDependencies multiSentence with
  | .ok (.ok document) =>
      unless document.results.size == 2 do
        throw <| IO.userError "exact enhanced graph limits changed the sentence count"
  | _ => throw <| IO.userError "exact enhanced graph limits were rejected"
  match ← NLP.runIO { maxGraphCandidates := 0, maxGraphEdges := 4 } <|
      NLP.enhanceDependencies multiSentence with
  | .ok (.skipped (.candidateLimit 1 0)) => pure ()
  | _ => throw <| IO.userError "candidate clamp lost its exact one-short boundary"
  match ← NLP.runIO { maxGraphCandidates := 1, maxGraphEdges := 3 } <|
      NLP.enhanceDependencies multiSentence with
  | .ok (.skipped (.workLimit 4 3)) => pure ()
  | _ => throw <| IO.userError "edge clamp lost its exact one-short boundary"
  let lexicalRequired ←
    match EnglishEnhanced.enhanceDocumentWith?
        { maxLexicalBytes := 0 } multiSentence with
    | .error (.sentence 1 2 5 (.lexicalBudget required 0)) => pure required
    | _ => throw <| IO.userError "pure lexical-byte budget did not reject the fixture"
  match ← NLP.runIO { maxGraphLexicalBytes := 0 } <|
      NLP.enhanceDependencies multiSentence with
  | .ok (.skipped (.byteLimit required 0)) =>
      unless required == lexicalRequired do
        throw <| IO.userError "lexical-byte clamp changed the exact required count"
  | _ => throw <| IO.userError "lexical-byte clamp lost its typed skip reason"

/-- Length policy runs before each sentence kernel and malformed input remains typed. -/
def testLengthAndInvalidInput : IO Unit := do
  match ← NLP.runIO { maxLen := 2 } <| NLP.enhanceDependencies multiSentence with
  | .ok (.skipped (.tooLong 3 2)) => pure ()
  | _ => throw <| IO.userError "enhancement did not enforce per-sentence maxLen"
  let malformed : Doc [.dep, .lemma, .pos, .sents, .tokens] :=
    { multiSentence with spans := #[⟨0, 4⟩] }
  match ← NLP.runIO {} <| NLP.enhanceDependencies malformed with
  | .error (.invalidInput location why) =>
      unless location.contains "tokens [0, 5)" && why.contains "semantic validation" do
        throw <| IO.userError "invalid enhanced input lost its document coordinates"
  | _ => throw <| IO.userError "malformed enhanced input crossed the checked boundary"

/-- Token-weighted default and explicit-grain batches preserve stable document order. -/
def testOrderedBatch : IO Unit := do
  let documents := #[multiSentence, singleton, multiSentence]
  let runtime : Nlp.Config :=
    { numThreads := 3
      parallelMinWeight := 1
      maxDedicatedThreads := 3 }
  match ← NLP.runIO runtime do
    let defaults ← NLP.enhanceDependenciesMany documents
    let explicitTokens ←
      NLP.enhanceDependenciesManyWithMinTokens 1 .default documents
    let explicitWork ←
      NLP.enhanceDependenciesManyWithMinWork 1 .default documents
    return (defaults, explicitTokens, explicitWork)
  with
  | .error cause => throw <| IO.userError s!"enhanced dependency batch failed: {cause}"
  | .ok (defaults, explicitTokens, explicitWork) =>
      let ordered := fun
          (output : Array (Analysis
            (EnglishEnhanced.Document [.dep, .lemma, .pos, .sents, .tokens]))) =>
        output.size == 3 &&
          match output[0]?, output[1]?, output[2]? with
          | some (Analysis.ok first), some (Analysis.ok second),
              some (Analysis.ok third) =>
              first.source.size == 5 && first.results.size == 2 &&
                second.source.size == 1 && second.results.size == 1 &&
                third.source.size == 5 && third.results.size == 2
          | _, _, _ => false
      unless ordered defaults && ordered explicitTokens && ordered explicitWork do
        throw <| IO.userError "weighted enhancement batch changed input order"

/-- Cancellation is observed before any enhanced-dependency sentence kernel starts. -/
def testCancelled : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <|
      (NLP.runIn env (NLP.enhanceDependencies multiSentence)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "enhanced dependency cancellation reason was lost"

#eval testEffectParity
#eval testRuntimeLimits
#eval testLengthAndInvalidInput
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.EnhancedDependency
