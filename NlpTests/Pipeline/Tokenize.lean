import Nlp.Pipeline.Tokenize

namespace NlpTests.Pipeline.Tokenize

open Nlp Nlp.Tokenize

private def tokenizer : Tokenizer := .default

private def tokenDoc : Doc [.tokens] :=
  tokenizer.tokenizeDoc "Marie was born in Paris."

example : tokenDoc.forms = #["Marie", "was", "born", "in", "Paris", "."] := by
  native_decide

example : tokenDoc.SemanticWF := by native_decide

example : (tokenizer.tokenizeDocChecked "Marie was born in Paris.").isOk := by
  native_decide

private def processed : Doc [.sents, .tokens] :=
  tokenizer.process "One sentence. Another one!"

example : processed.sentEnd = #[3, 6] := by native_decide
example : processed.SemanticWF := by native_decide

private def rawWithStaleColumns : Doc [] :=
  { text := "fresh text", pos := #["STALE"], head := #[99], deprel := #["stale"] }

private def exactResult : Doc [.tokens] :=
  tokenizer.annotator rawWithStaleColumns

example : exactResult.forms = #["fresh", "text"] := by native_decide
example : exactResult.pos = #[] := by native_decide
example : exactResult.head = #[] := by native_decide
example : exactResult.deprel = #[] := by native_decide

private structure Snapshot where
  text : String
  spans : Array Span
  forms : Array String
  sentEnd : Array Nat
  deriving Repr, DecidableEq

private def snapshot (doc : Doc ls) : Snapshot :=
  ⟨doc.text, doc.spans, doc.forms, doc.sentEnd⟩

private def pureSnapshots (texts : Array String) : Array Snapshot :=
  texts.map fun text ↦ snapshot (tokenizer.process text)

private def testSingle : IO Unit := do
  match ← NLP.runIO {} (NLP.processText tokenizer "Hi. Bye!") with
  | .ok doc =>
      if snapshot doc != snapshot (tokenizer.process "Hi. Bye!") then
        throw <| IO.userError "effectful tokenization changed the pure result"
  | .error cause =>
      throw <| IO.userError s!"effectful tokenization failed: {cause}"

private def testWeightedCorpus : IO Unit := do
  let texts := #["A.", String.ofList (List.replicate 4096 'x') ++ ".", "B!", "C?"]
  let config : Nlp.Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config (NLP.processTexts tokenizer texts) with
  | .ok documents =>
      if documents.map snapshot != pureSnapshots texts then
        throw <| IO.userError "weighted corpus tokenization changed order or output"
      if !documents.all fun doc ↦ decide doc.SemanticWF then
        throw <| IO.userError "weighted corpus returned a semantically invalid document"
  | .error cause =>
      throw <| IO.userError s!"weighted corpus tokenization failed: {cause}"

private def testSerialParallelEquality : IO Unit := do
  let texts := #["one", "two words", "Three. Four!", "😀 Unicode.", "last"]
  let serial : Nlp.Config := { numThreads := 1, parallelMinWeight := 1 }
  let parallel : Nlp.Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  let serialResult ← NLP.runIO serial (NLP.tokenizeTexts tokenizer texts)
  let parallelResult ← NLP.runIO parallel (NLP.tokenizeTexts tokenizer texts)
  match serialResult, parallelResult with
  | .ok left, .ok right =>
      if left.map snapshot != right.map snapshot then
        throw <| IO.userError "serial and parallel tokenization diverged"
  | _, _ => throw <| IO.userError "serial or parallel tokenization failed"

private def testPreCancelled : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .cancel
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.tokenizeText tokenizer "cancel me")).toBaseIO with
  | .error (.cancelled .cancel) => pure ()
  | _ => throw <| IO.userError "tokenization ignored pre-existing cancellation"

#eval testSingle
#eval testWeightedCorpus
#eval testSerialParallelEquality
#eval testPreCancelled

end NlpTests.Pipeline.Tokenize
