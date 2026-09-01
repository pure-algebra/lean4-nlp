import Nlp.Pipeline.Graph

/-! # Effectful bounded dependency-graph query tests -/

namespace NlpTests.Pipeline.Graph

open Nlp Nlp.Dependency Nlp.Pattern Nlp.Pattern.GraphQuery

/-- Compile checked rows to an attribute-free pipeline input. -/
private def inputOfRows? (rows : Array (Row String)) : Option Input :=
  match Nlp.Dependency.Graph.ofRows rows with
  | .error _ => none
  | .ok graph =>
      some { graph, attributes := Array.replicate graph.nodeCount {} }

private def oneNode : Option Input :=
  inputOfRows? #[⟨.word 1, #[⟨.root, "root", .basic⟩]⟩]

private def twoNodes : Option Input :=
  inputOfRows?
    #[⟨.word 1, #[⟨.root, "root", .basic⟩]⟩,
      ⟨.word 2, #[⟨.word 1, "dep", .basic⟩]⟩]

private def threeNodes : Option Input :=
  inputOfRows?
    #[⟨.word 1, #[⟨.word 2, "nsubj", .basic⟩]⟩,
      ⟨.word 2, #[⟨.root, "root", .basic⟩]⟩,
      ⟨.word 3, #[⟨.word 2, "obj", .basic⟩]⟩]

private def anyQuery : Query := .node .any

/-- Compact outcome used to assert stable batch order across dependent executions. -/
private def status {config : ExecutionConfig} : Analysis (Execution config) → Nat
  | .ok execution => execution.result.items.size
  | .skipped (.tooLong tokens _) => 100 + tokens
  | .skipped _ => 900
  | .noAnalysis => 999

-- Raw and validate-once functional facades preserve parity and exact query provenance.
#guard
  match threeNodes, anyQuery.check with
  | some input, .ok checked =>
      match executePureWith {} 3 input anyQuery,
          executeCheckedPureWith {} 3 input checked with
      | .ok (.ok raw), .ok (.ok validated) =>
          raw.result.referenceView == validated.result.referenceView &&
            validated.result.referenceView == referenceFindAll validated.index anyQuery &&
            decide (validated.query = anyQuery)
      | _, _ => false
  | _, _ => false

-- Runtime length equality succeeds and one-short length is policy data rather than a failure.
#guard
  match threeNodes with
  | none => false
  | some input =>
      let exact :=
        match executePureWith {} 3 input anyQuery with
        | .ok (.ok execution) => execution.result.items.size == 4
        | _ => false
      let oneShort :=
        match executePureWith {} 2 input anyQuery with
        | .ok (.skipped (.tooLong 3 2)) => true
        | _ => false
      exact && oneShort

-- Index, query-work, match, and lexical limits are translated to their typed skip classes.
#guard
  match threeNodes with
  | none => false
  | some input =>
      match executePureWith {} 10 input anyQuery with
      | .ok (.ok baseline) =>
          let nodeLow : ExecutionConfig :=
            { index := { maxNodes := 2, maxEdges := 3, maxLexicalBytes := 12 } }
          let workLow : ExecutionConfig :=
            { search := { maxWork := baseline.result.work - 1 } }
          let workExact : ExecutionConfig :=
            { search := { maxWork := baseline.result.work } }
          let matchesLow : ExecutionConfig := { search := { maxMatches := 0 } }
          let bytesLow : ExecutionConfig :=
            { search := { maxQueryLexicalBytes := 2 } }
          let nodeSkipped :=
            match executePureWith nodeLow 10 input anyQuery with
            | .ok (.skipped (.workLimit 3 2)) => true
            | _ => false
          let workSkipped :=
            match executePureWith workLow 10 input anyQuery with
            | .ok (.skipped (.workLimit required limit)) =>
                required == baseline.result.work && limit == baseline.result.work - 1
            | _ => false
          let workExactOk :=
            match executePureWith workExact 10 input anyQuery with
            | .ok (.ok execution) => execution.result.work == baseline.result.work
            | _ => false
          let matchSkipped :=
            match executePureWith matchesLow 10 input anyQuery with
            | .ok (.skipped (.candidateLimit 1 0)) => true
            | _ => false
          let lexicalQuery : Query := .node (.attribute .form "abc")
          let bytesSkipped :=
            match executePureWith bytesLow 10 input lexicalQuery with
            | .ok (.skipped (.byteLimit 3 2)) => true
            | _ => false
          let coordinateQuery : Query := .node (.node (.word 4_294_967_296))
          let coordinateSkipped :=
            match executePureWith {} 10 input coordinateQuery with
            | .ok (.skipped (.workLimit 4_294_967_296 4_294_967_295)) => true
            | _ => false
          nodeSkipped && workSkipped && workExactOk && matchSkipped && bytesSkipped &&
            coordinateSkipped
      | _ => false

-- Misaligned graph attributes remain malformed data, never a resource skip.
#guard
  match oneNode with
  | none => false
  | some input =>
      let malformed : Input := { input with attributes := #[] }
      match executePureWith {} 10 malformed anyQuery with
      | .error (.attributeCount 1 0) => true
      | _ => false

-- Dynamic comparison bytes accept the exact total and map one-short failures to byte limits.
#guard
  match twoNodes with
  | none => false
  | some input =>
      let query : Query := .outgoing (.equal "dep") (.node .any)
      let exact : ExecutionConfig := { search := { maxComparisonBytes := 13 } }
      let low : ExecutionConfig := { search := { maxComparisonBytes := 12 } }
      let exactAccepted :=
        match executePureWith exact 2 input query with
        | .ok (.ok execution) => execution.result.comparisonBytes == 13
        | _ => false
      let lowSkipped :=
        match executePureWith low 2 input query with
        | .ok (.skipped (.byteLimit required limit)) => required == 13 && limit == 12
        | _ => false
      exactAccepted && lowSkipped

-- Retained indices reapply their cached lexical total at the exact and one-short boundaries.
#guard
  match threeNodes with
  | none => false
  | some input =>
      match executePureWith {} 3 input anyQuery with
      | .ok (.ok baseline) =>
          let bytes := baseline.index.lexicalBytes
          let exact : ExecutionConfig := { index := { maxLexicalBytes := bytes } }
          let low : ExecutionConfig := { index := { maxLexicalBytes := bytes - 1 } }
          let exactAccepted :=
            match executeIndexPureWith exact 3 baseline.index anyQuery with
            | .ok (.ok _) => true
            | _ => false
          let lowSkipped :=
            match executeIndexPureWith low 3 baseline.index anyQuery with
            | .ok (.skipped (.byteLimit required limit)) =>
                required == bytes && limit == bytes - 1
            | _ => false
          exactAccepted && lowSkipped
      | _ => false

private def testEffectfulParity : IO Unit := do
  let input ←
    match threeNodes with
    | some value => pure value
    | none => throw <| IO.userError "graph parity fixture did not compile"
  let checked ←
    match anyQuery.check with
    | .ok value => pure value
    | .error _ => throw <| IO.userError "valid graph query failed preflight"
  let pureResult := executeCheckedPureWith {} 3 input checked
  let effectResult ← NLP.runIO { maxLen := 3 } <|
    NLP.queryGraphCheckedWith {} input checked
  match pureResult, effectResult with
  | .ok (.ok pureExecution), .ok (.ok effectExecution) =>
      if pureExecution.result.referenceView != effectExecution.result.referenceView ||
          pureExecution.result.work != effectExecution.result.work ||
          pureExecution.result.states != effectExecution.result.states ||
          pureExecution.result.comparisonBytes != effectExecution.result.comparisonBytes then
        throw <| IO.userError "effectful graph query changed the pure result"
  | _, _ => throw <| IO.userError "valid pure/effectful graph query failed"

private def testPrecompiledIndex : IO Unit := do
  let input ←
    match threeNodes with
    | some value => pure value
    | none => throw <| IO.userError "precompiled-index fixture did not compile"
  let baseline ←
    match executePureWith {} 3 input anyQuery with
    | .ok (.ok execution) => pure execution
    | _ => throw <| IO.userError "precompiled-index baseline failed"
  let checked ←
    match anyQuery.check with
    | .ok value => pure value
    | .error _ => throw <| IO.userError "valid retained-index query failed preflight"
  match ← NLP.runIO { maxLen := 3 }
      (NLP.queryGraphIndexCheckedWith {} baseline.index checked) with
  | .ok (.ok execution) =>
      if execution.result.referenceView != baseline.result.referenceView ||
          execution.result.work != baseline.result.work ||
          execution.result.states != baseline.result.states ||
          execution.result.comparisonBytes != baseline.result.comparisonBytes then
        throw <| IO.userError "precompiled-index execution changed the pure result"
  | _ => throw <| IO.userError "valid precompiled-index execution failed"

private def testInvalidGraph : IO Unit := do
  let input ←
    match oneNode with
    | some value => pure value
    | none => throw <| IO.userError "invalid graph fixture did not compile"
  let malformed : Input := { input with attributes := #[] }
  match ← NLP.runIO {} (NLP.queryGraph malformed anyQuery) with
  | .error (.invalidInput "dependency graph query input" detail) =>
      if !detail.contains "1 nodes but 0 attribute" then
        throw <| IO.userError "invalid graph lost its alignment detail"
  | _ => throw <| IO.userError "invalid graph did not become Fail.invalidInput"

private def testStableBatch : IO Unit := do
  let inputs ←
    match oneNode, threeNodes, twoNodes with
    | some one, some three, some two => pure #[one, three, two]
    | _, _, _ => throw <| IO.userError "ordered graph fixtures did not compile"
  let runtime : Nlp.Config :=
    { numThreads := 3, maxLen := 2, parallelMinWeight := 1,
      maxDedicatedThreads := 3 }
  let checked ←
    match anyQuery.check with
    | .ok value => pure value
    | .error _ => throw <| IO.userError "valid batch query failed preflight"
  match ← NLP.runIO runtime do
      let checkedExplicit ← NLP.queryGraphsManyCheckedWithMinWork 1 {} inputs checked
      let checkedDefaults ← NLP.queryGraphsManyCheckedWith {} inputs checked
      let rawDefaults ← NLP.queryGraphsMany inputs anyQuery
      return (checkedExplicit, checkedDefaults, rawDefaults) with
  | .ok (checkedExplicit, checkedDefaults, rawDefaults) =>
      if checkedExplicit.map status != #[2, 103, 3] ||
          checkedDefaults.map status != #[2, 103, 3] ||
          rawDefaults.map status != #[2, 103, 3] then
        throw <| IO.userError "parallel graph queries lost stable input order"
  | .error cause => throw <| IO.userError s!"parallel graph query failed: {cause}"

private def testCancelled : IO Unit := do
  let input ←
    match threeNodes with
    | some value => pure value
    | none => throw <| IO.userError "cancellation graph fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.queryGraph input anyQuery)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "graph query lost its cancellation reason"

private def testCancelledInvalidBatch : IO Unit := do
  let input ←
    match oneNode with
    | some value => pure value
    | none => throw <| IO.userError "cancelled batch fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  let invalid : Query := .same ""
  match ← liftM <| (NLP.runIn env (NLP.queryGraphsMany #[input] invalid)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "batch classified invalid preflight after cancellation"

#eval testEffectfulParity
#eval testPrecompiledIndex
#eval testInvalidGraph
#eval testStableBatch
#eval testCancelled
#eval testCancelledInvalidBatch

end NlpTests.Pipeline.Graph
