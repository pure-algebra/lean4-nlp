import Nlp.Pipeline.Annotate

namespace NlpTests.Pipeline.Annotate

open Nlp

private def markPos : Ann Id [.tokens] [.pos] :=
  Ann.fromPure "pos" fun _ doc ↦ { doc with pos := doc.forms.map fun _ ↦ "NN" }

private def tokenDoc (word : String) : Doc [.tokens] :=
  { text := word, forms := #[word], spans := #[⟨0, word.length⟩] }

example : (markPos.run (by decide) (tokenDoc "dog")).pos = #["NN"] := by
  native_decide

example : (Ann.lift (M := NLP) markPos).name = "pos" := by
  rfl

private def testOne : IO Unit := do
  match ← NLP.runIO {} (NLP.annotatePure markPos (tokenDoc "dog")) with
  | .ok doc =>
      if doc.pos != #["NN"] then
        throw <| IO.userError "effectful single annotation changed the pure result"
  | .error _ => throw <| IO.userError "effectful single annotation failed"

private def testMany : IO Unit := do
  let input := #[tokenDoc "a", tokenDoc "b", tokenDoc "c", tokenDoc "d"]
  let config : Config := {
    numThreads := 4
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config (NLP.annotateManyPure markPos input) with
  | .ok output =>
      if output.map (fun doc ↦ doc.text) != #["a", "b", "c", "d"] then
        throw <| IO.userError "parallel annotation did not preserve input order"
      if !output.all (fun doc ↦ doc.pos == #["NN"]) then
        throw <| IO.userError "parallel annotation changed a pure result"
  | .error _ => throw <| IO.userError "parallel annotation failed"

private def testFailure : IO Unit := do
  let worker (value : Nat) : NLP Nat := do
    if value == 2 then
      throw <| .invalidInput "item 2" "expected"
    return value + 1
  let config : Config := {
    numThreads := 4
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config (NLP.traverseArray #[0, 1, 2, 3] worker) with
  | .error (.invalidInput "item 2" "expected") => pure ()
  | _ => throw <| IO.userError "array traversal did not preserve the typed failure"

#eval testOne
#eval testMany
#eval testFailure

end NlpTests.Pipeline.Annotate
