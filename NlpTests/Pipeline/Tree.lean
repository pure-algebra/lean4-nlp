import Nlp.Pipeline.Tree

/-! Functional/effectful typed tree-query boundary tests. -/

namespace NlpTests.Pipeline.Tree

open Nlp Nlp.Pattern.TreeQuery

/-- A branching source with two noun phrases and three terminals. -/
private def sample : NamedTree :=
  .node "S" (.node "NP" (.leaf "cats") #[])
    #[.node "VP" (.leaf "chase") #[.node "NP" (.leaf "mice") #[]]]

/-- A one-token source makes ordered batch output observable. -/
private def singleton : NamedTree := .node "NN" (.leaf "cat") #[]

/-- The pure convenience boundary retains deterministic matching preorder nodes. -/
example :
    (match execute (.label "NP") sample with
    | .ok result => result.nodes == #[1, 5]
    | .error _ => false) = true := by
  native_decide

/-- The preferred effectful facade returns the same certified result as the pure API. -/
def testEffectParity : IO Unit := do
  let .ok expected := execute (.child (.label "NP")) sample
    | throw <| IO.userError "pure tree-query fixture failed"
  match ← NLP.runIO {} <| NLP.matchTree (.child (.label "NP")) sample with
  | .ok (.ok actual) =>
      unless actual.nodes == expected.nodes && actual.tokenCount == expected.tokenCount do
        throw <| IO.userError "effectful tree-query execution diverged from the pure API"
  | _ => throw <| IO.userError "valid effectful tree query was not analyzed"

/-- Runtime length and exact arena/search budgets become typed analysis outcomes. -/
def testLimits : IO Unit := do
  match ← NLP.runIO { maxLen := 2 } <| NLP.matchTree .any sample with
  | .ok (.skipped (.tooLong 3 2)) => pure ()
  | _ => throw <| IO.userError "tree-query execution ignored runtime maxLen"
  match ← NLP.runIO {} <|
      NLP.matchTreeWith { maxNodes := 6 } {} {} .any sample with
  | .ok (.skipped (.workLimit 7 6)) => pure ()
  | _ => throw <| IO.userError "tree-arena node limit lost its exact first unit"
  match ← NLP.runIO {} <|
      NLP.matchTreeWith {} {} { maxMatches := 0 } .any sample with
  | .ok (.skipped (.candidateLimit 1 0)) => pure ()
  | _ => throw <| IO.userError "tree-query match limit lost its exact first unit"

/-- Query compilation limits are analysis data, while standalone compilation remains explicit. -/
def testCompileLimits : IO Unit := do
  match ← NLP.runIO {} <| NLP.matchTreeWith {} { maxPatternNodes := 0 } {} .any sample with
  | .ok (.skipped (.workLimit 1 0)) => pure ()
  | _ => throw <| IO.userError "tree-query compilation limit was not a typed skip"
  match ← NLP.runIO {} <| NLP.compileTreeQueryWith { maxPatternNodes := 0 } .any with
  | .error (.invalidConfig why) =>
      unless why.contains "1 constructors" && why.contains "limit is 0" do
        throw <| IO.userError "standalone tree-query compiler lost its exact limit"
  | _ => throw <| IO.userError "standalone compiler accepted a zero query-node budget"

/-- Compile-once parallel batches preserve stable source order. -/
def testOrderedBatch : IO Unit := do
  let sources := #[sample, singleton, sample]
  let runtime : Nlp.Config :=
    { numThreads := 3, parallelMinGrain := 1, parallelMinWeight := 1,
      maxDedicatedThreads := 3 }
  match ← NLP.runIO runtime do
      let explicit ← NLP.matchTreesWithMinWork 1 {} {} {} .any sources
      let defaults ← NLP.matchTrees .any sources
      return (explicit, defaults) with
  | .error cause => throw <| IO.userError s!"tree-query batch failed: {cause}"
  | .ok (explicit, defaults) =>
      for output in #[explicit, defaults] do
        unless output.size == 3 do
          throw <| IO.userError "tree-query batch changed the source count"
        match output[0]?, output[1]?, output[2]? with
        | some (Analysis.ok first), some (Analysis.ok second), some (Analysis.ok third) =>
            unless first.tokenCount == 3 && second.tokenCount == 1 && third.tokenCount == 3 do
              throw <| IO.userError "tree-query batch changed stable source order"
        | _, _, _ => throw <| IO.userError "tree-query batch did not analyze every source"

/-- A pre-cancelled environment stops before compilation or arena construction. -/
def testCancelled : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.matchTree .any sample)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "tree-query execution lost its cancellation reason"

#eval testEffectParity
#eval testLimits
#eval testCompileLimits
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.Tree
