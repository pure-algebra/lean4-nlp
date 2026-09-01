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

/-- Serial indexed traversal exposes exact original positions in stable order. -/
private def testIndexedSerial : IO Unit := do
  let input := #["zero", "one", "two", "three"]
  let expected := #[(0, "zero"), (1, "one"), (2, "two"), (3, "three")]
  match ← NLP.runIO { numThreads := 1 } <|
      NLP.traverseArrayIndexed input fun index value ↦ pure (index, value) with
  | .ok output =>
      if output != expected then
        throw <| IO.userError "serial indexed traversal changed an index or item"
  | .error cause => throw <| IO.userError s!"serial indexed traversal failed: {cause}"
  match ← NLP.runIO { numThreads := 1 } <|
      NLP.traverseArrayWeightedIndexed input String.length fun index value ↦
        pure (index, value) with
  | .ok output =>
      if output != expected then
        throw <| IO.userError "serial weighted indexed traversal changed stable order"
  | .error cause =>
      throw <| IO.userError s!"serial weighted indexed traversal failed: {cause}"

/-- Parallel indexed traversal retains original indices when an earlier chunk finishes later. -/
private def testIndexedParallel : IO Unit := do
  let input := #[3, 1, 4, 1, 5, 9, 2, 6]
  let config : Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config <|
      NLP.traverseArrayWeightedIndexedWithMinWeight 1 input (fun _ ↦ 1) fun index value ↦ do
        if index = 0 then
          liftM <| IO.sleep 10
        return (index, value) with
  | .ok output =>
      if output != #[(0, 3), (1, 1), (2, 4), (3, 1), (4, 5), (5, 9), (6, 2), (7, 6)] then
        throw <| IO.userError "parallel weighted indexed traversal lost stable indices"
  | .error cause =>
      throw <| IO.userError s!"parallel weighted indexed traversal failed: {cause}"

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

/-- A single-chunk indexed traversal reports the lowest failing original item. -/
private def testIndexedSerialFailureOrder : IO Unit := do
  let worker (index value : Nat) : NLP Nat := do
    if index == 1 || index == 3 then
      throw <| .invalidInput s!"item {index}" "expected indexed failure"
    return value
  match ← NLP.runIO { numThreads := 4 } <|
      NLP.traverseArrayIndexedWithGrain 99 (Array.range 5) worker with
  | .error (.invalidInput "item 1" "expected indexed failure") => pure ()
  | _ => throw <| IO.userError "serial indexed traversal lost lowest failure order"

/-- Parallel failure collection remains ordered by original index, not completion time. -/
private def testIndexedParallelFailureOrder : IO Unit := do
  let worker (index value : Nat) : NLP Nat := do
    if index = 0 then
      liftM <| IO.sleep 25
    if index == 0 || index == 6 then
      throw <| .invalidInput s!"item {index}" "expected racing indexed failure"
    return value
  let config : Config := {
    numThreads := 4
    parallelMinWeight := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config <|
      NLP.traverseArrayWeightedIndexedWithMinWeight 1 (Array.range 8) (fun _ ↦ 1) worker with
  | .error (.invalidInput "item 0" "expected racing indexed failure") => pure ()
  | _ => throw <| IO.userError "parallel indexed traversal lost lowest failure order"

#eval testOne
#eval testMany
#eval testIndexedSerial
#eval testIndexedParallel
#eval testFailure
#eval testIndexedSerialFailureOrder
#eval testIndexedParallelFailureOrder

end NlpTests.Pipeline.Annotate
