import Nlp.Pattern.Graph
import Nlp.Pipeline.Annotate

/-!
# Effectful bounded dependency-graph queries

The pure facade compiles each checked dependency graph exactly once and retains that index beside
its dependent query result. The `NLP` facade adds sentence-length policy, typed input failures,
cooperative cancellation, and stable work-weighted batch traversal.
-/

namespace Nlp.Pattern.GraphQuery

open Nlp.Dependency

/-- Index and search policies used by one graph-query execution. -/
structure ExecutionConfig where
  /-- Limits for compiling the immutable dual graph index. -/
  index : IndexConfig := {}
  /-- Limits for bounded query preflight and evaluation. -/
  search : SearchConfig := {}
  deriving Repr, DecidableEq, Inhabited

/-- One checked dependency graph and its aligned optional lexical columns. -/
structure Input where
  graph : Dependency.Graph String
  attributes : Array NodeAttributes

namespace Input

/-- Exact deterministic index-storage scheduling weight without constructing an index. -/
def work (input : Input) : Nat :=
  input.graph.nodeCount + input.graph.edgeCount +
    requiredLexicalBytes input.graph input.attributes + 1

end Input

/-- A dependent search result packaged with the exact immutable index that types it. -/
structure Execution (config : ExecutionConfig) where
  private mk ::
  /-- Index compiled once from the source graph and retained lexical columns. -/
  index : Index
  /-- Bounded result whose matches are certified against `index`. -/
  result : Result index config.search

namespace Execution

/-- Package a certified result with the exact immutable index that types it. -/
@[inline] def ofResult (index : Index) (result : Result index config.search) :
    Execution config :=
  ⟨index, result⟩

/-- Original structurally validated query evaluated by this execution. -/
@[inline] def query {config : ExecutionConfig} (execution : Execution config) : Query :=
  execution.result.query

/-- Execution provenance retains the query's exact successful preflight outcome. -/
theorem query_wellFormed {config : ExecutionConfig} (execution : Execution config) :
    execution.result.checkedQuery.WF :=
  execution.result.query_wellFormed

end Execution

/-- Malformed source/query data or an impossible protected-index failure. -/
inductive InputError where
  | attributeCount (expected found : Nat)
  | missingHead (edge : Nat) (head : NodeId)
  | inconsistentIndex
  | emptyBindingName
  deriving Repr, DecidableEq, Inhabited

namespace InputError

/-- Stable detail used by the effectful `Fail.invalidInput` translation. -/
def detail : InputError → String
  | .attributeCount expected found =>
      s!"graph has {expected} nodes but {found} attribute records"
  | .missingHead edge head =>
      s!"graph-query index edge {edge} names missing head {repr head}"
  | .inconsistentIndex => "graph-query index failed its protected storage invariant"
  | .emptyBindingName => "graph query contains an empty binding or backreference name"

end InputError

/-- Classify every graph-index failure as a resource skip or malformed input. -/
private def classifyIndexError : IndexError → SkipReason ⊕ InputError
  | .nodeBudget required limit => .inl (.workLimit required limit)
  | .edgeBudget required limit => .inl (.workLimit required limit)
  | .lexicalByteBudget required limit => .inl (.byteLimit required limit)
  | .coordinateBudget required limit => .inl (.workLimit required limit)
  | .attributeCount expected found => .inr (.attributeCount expected found)
  | .missingHead edge head => .inr (.missingHead edge head)
  | .inconsistentStorage => .inr .inconsistentIndex

/-- Classify every query failure as a resource skip or malformed input. -/
private def classifySearchError : SearchError → SkipReason ⊕ InputError
  | .workBudget required limit => .inl (.workLimit required limit)
  | .comparisonByteBudget required limit => .inl (.byteLimit required limit)
  | .stateBudget required limit => .inl (.workLimit required limit)
  | .matchBudget required limit => .inl (.candidateLimit required limit)
  | .queryNodeBudget required limit => .inl (.workLimit required limit)
  | .queryDepthBudget required limit => .inl (.workLimit required limit)
  | .queryLexicalByteBudget required limit => .inl (.byteLimit required limit)
  | .queryCoordinateBudget required limit => .inl (.workLimit required limit)
  | .emptyBindingName => .inr .emptyBindingName
  | .inconsistentIndex => .inr .inconsistentIndex

/-- Convert one classified failure into a typed functional non-result or input error. -/
private def classifiedFailure (cause : SkipReason ⊕ InputError) :
    Except InputError (Analysis α) :=
  match cause with
  | .inl reason => .ok (.skipped reason)
  | .inr malformed => .error malformed

/-- Convert a classified search failure into the public functional outcome. -/
private def searchFailure {config : ExecutionConfig} (cause : SearchError) :
    Except InputError (Analysis (Execution config)) :=
  classifiedFailure (classifySearchError cause)

/-- Reapply an index policy to a retained index without rebuilding its immutable storage. -/
private def retainedIndexSkipReason? (config : IndexConfig) (index : Index) :
    Option SkipReason :=
  if config.maxNodes < index.graph.nodeCount then
    some (.workLimit index.graph.nodeCount config.maxNodes)
  else if config.maxEdges < index.graph.edgeCount then
    some (.workLimit index.graph.edgeCount config.maxEdges)
  else if config.maxCoordinate < index.coordinateMaximum then
    some (.workLimit index.coordinateMaximum config.maxCoordinate)
  else
    let bytes := index.lexicalBytes
    if config.maxLexicalBytes < bytes then
      some (.byteLimit bytes config.maxLexicalBytes)
    else
      none

/-- Validate retained-index policy after query preflight without rebuilding immutable storage. -/
private def prepareRetainedCheckedWith (config : ExecutionConfig) (maxLen : Nat)
    (index : Index) : Except InputError (Analysis Index) := do
  if maxLen < index.graph.nodeCount then
    return .skipped (.tooLong index.graph.nodeCount maxLen)
  if let some reason := retainedIndexSkipReason? config.index index then
    return .skipped reason
  return .ok index

/-- Validate input policy after query preflight and compile exactly one immutable index. -/
private def prepareInputCheckedWith (config : ExecutionConfig) (maxLen : Nat)
    (input : Input) : Except InputError (Analysis Index) := do
  if input.attributes.size != input.graph.nodeCount then
    throw <| .attributeCount input.graph.nodeCount input.attributes.size
  if maxLen < input.graph.nodeCount then
    return .skipped (.tooLong input.graph.nodeCount maxLen)
  match Index.compileWith config.index input.graph input.attributes with
  | .error cause => classifiedFailure (classifyIndexError cause)
  | .ok index => return .ok index

/-- Run one already validated query against a retained index without rebuilding either. -/
def executeIndexCheckedPureWith (config : ExecutionConfig) (maxLen : Nat) (index : Index)
    (checked : CheckedQuery config.search) :
    Except InputError (Analysis (Execution config)) := do
  match ← prepareRetainedCheckedWith config maxLen index with
  | .skipped reason => return .skipped reason
  | .noAnalysis => return .noAnalysis
  | .ok prepared =>
      match findAllCheckedWith prepared checked with
      | .ok result => return .ok (Execution.ofResult prepared result)
      | .error cause => searchFailure cause

/-- Validate once, then query an already compiled index without rebuilding it. -/
def executeIndexPureWith (config : ExecutionConfig) (maxLen : Nat) (index : Index)
    (query : Query) : Except InputError (Analysis (Execution config)) := do
  match query.checkWith config.search with
  | .error cause => searchFailure cause
  | .ok checked => executeIndexCheckedPureWith config maxLen index checked

/-- Compile and run one already validated query through the pure functional facade. -/
def executeCheckedPureWith (config : ExecutionConfig) (maxLen : Nat) (input : Input)
    (checked : CheckedQuery config.search) :
    Except InputError (Analysis (Execution config)) := do
  match ← prepareInputCheckedWith config maxLen input with
  | .skipped reason => return .skipped reason
  | .noAnalysis => return .noAnalysis
  | .ok index =>
      match findAllCheckedWith index checked with
      | .ok result => return .ok (Execution.ofResult index result)
      | .error cause => searchFailure cause

/--
Compile and run one graph query through the pure functional facade.

Attribute alignment and query shape are checked before length policy; the graph index is then
compiled once, queried once, and retained in the successful `Execution` value.
-/
def executePureWith (config : ExecutionConfig) (maxLen : Nat) (input : Input)
    (query : Query) : Except InputError (Analysis (Execution config)) := do
  if input.attributes.size != input.graph.nodeCount then
    throw <| .attributeCount input.graph.nodeCount input.attributes.size
  match query.checkWith config.search with
  | .error cause => searchFailure cause
  | .ok checked => executeCheckedPureWith config maxLen input checked

/-- Run one graph query under production index, query, and length limits. -/
@[inline] def executePure (input : Input) (query : Query) :
    Except InputError (Analysis (Execution {})) :=
  executePureWith {} ({} : Nlp.Config).maxLen input query

end Nlp.Pattern.GraphQuery

namespace Nlp.NLP

open Pattern.GraphQuery

/-- Lift a pure graph-query outcome while preserving its stable input location. -/
private def liftGraphOutcome (location : String)
    (outcome : Except InputError (Analysis (Execution config))) :
    NLP (Analysis (Execution config)) :=
  match outcome with
  | .ok analysis => pure analysis
  | .error cause =>
      match cause with
      | .attributeCount .. | .emptyBindingName =>
          throw <| .invalidInput location cause.detail
      | .missingHead .. | .inconsistentIndex =>
          throw <| .modelCorrupt location cause.detail

/--
Run a prepared index with exact global counters and one cancellation boundary per anchor.

One high-fan-out anchor remains an indivisible pure kernel, so cancellation latency is bounded by
one anchor's configured work and comparison-byte limits rather than by the complete graph.
-/
private def queryPreparedIndexCheckedAt (location : String) (config : ExecutionConfig)
    (index : Index) (checked : CheckedQuery config.search) :
    NLP (Analysis (Execution config)) := do
  let mut cursor := SearchCursor.startChecked index checked
  checkCancelled
  for _ in [0:index.nodeCount] do
    checkCancelled
    let advanced := cursor.advance
    checkCancelled
    match advanced with
    | .ok value => cursor := value
    | .error cause => return ← liftGraphOutcome location (searchFailure cause)
  checkCancelled
  match cursor.result? with
  | some result => return .ok (Execution.ofResult index result)
  | none => liftGraphOutcome location (.error .inconsistentIndex)

/-- Effectful kernel for one query whose bounded preflight already succeeded. -/
private def queryGraphCheckedAt (location : String) (config : ExecutionConfig)
    (input : Input) (checked : CheckedQuery config.search) :
    NLP (Analysis (Execution config)) := do
  checkCancelled
  let runtime := (← read).config
  let prepared := prepareInputCheckedWith config runtime.maxLen input
  checkCancelled
  match prepared with
  | .error cause => liftGraphOutcome location (.error cause)
  | .ok (.skipped reason) => return .skipped reason
  | .ok .noAnalysis => return .noAnalysis
  | .ok (.ok index) => queryPreparedIndexCheckedAt location config index checked

/-- Effectful implementation that validates one query before delegating to the checked kernel. -/
private def queryGraphAt (location : String) (config : ExecutionConfig)
    (input : Input) (query : Query) : NLP (Analysis (Execution config)) := do
  checkCancelled
  if input.attributes.size != input.graph.nodeCount then
    let cause := InputError.attributeCount input.graph.nodeCount input.attributes.size
    return ← liftGraphOutcome location (.error cause)
  let checkedOutcome := query.checkWith config.search
  checkCancelled
  match checkedOutcome with
  | .error cause => liftGraphOutcome location (searchFailure cause)
  | .ok checked => queryGraphCheckedAt location config input checked

/-- Query one retained index with a query whose bounded preflight already succeeded. -/
def queryGraphIndexCheckedWith (config : ExecutionConfig) (index : Index)
    (checked : CheckedQuery config.search) : NLP (Analysis (Execution config)) := do
  checkCancelled
  let runtime := (← read).config
  let prepared := prepareRetainedCheckedWith config runtime.maxLen index
  checkCancelled
  match prepared with
  | .error cause => liftGraphOutcome "dependency graph query index" (.error cause)
  | .ok (.skipped reason) => return .skipped reason
  | .ok .noAnalysis => return .noAnalysis
  | .ok (.ok retained) =>
      queryPreparedIndexCheckedAt "dependency graph query index" config retained checked

/-- Query one already compiled index with runtime length and cancellation policy. -/
def queryGraphIndexWith (config : ExecutionConfig) (index : Index) (query : Query) :
    NLP (Analysis (Execution config)) := do
  checkCancelled
  let checkedOutcome := query.checkWith config.search
  checkCancelled
  match checkedOutcome with
  | .error cause =>
      liftGraphOutcome "dependency graph query index" (searchFailure cause)
  | .ok checked => queryGraphIndexCheckedWith config index checked

/-- Compile and run one already validated query through the preferred effectful boundary. -/
@[inline] def queryGraphCheckedWith (config : ExecutionConfig) (input : Input)
    (checked : CheckedQuery config.search) : NLP (Analysis (Execution config)) :=
  queryGraphCheckedAt "dependency graph query input" config input checked

/-- Compile and query one graph through the preferred effectful boundary. -/
@[inline] def queryGraphWith (config : ExecutionConfig) (input : Input) (query : Query) :
    NLP (Analysis (Execution config)) :=
  queryGraphAt "dependency graph query input" config input query

/-- Compile and query one graph under production graph-query policies. -/
@[inline] def queryGraph (input : Input) (query : Query) :
    NLP (Analysis (Execution {})) :=
  queryGraphWith {} input query

/-- Validate batch attribute alignment in stable order before launching any worker. -/
private def validateBatchInputs (inputs : Array Input) : NLP Unit := do
  for index in [0:inputs.size] do
    checkCancelled
    match inputs[index]? with
    | none =>
        throw <| .invalidConfig "graph-query batch escaped its source array"
    | some input =>
        if input.attributes.size != input.graph.nodeCount then
          let cause := InputError.attributeCount input.graph.nodeCount input.attributes.size
          throw <| .invalidInput s!"dependency graph query input {index}" cause.detail

/-- Schedule one shared checked query with stable work-weighted result order. -/
private def queryGraphsManyPreparedCore (minWork : Option Nat) (config : ExecutionConfig)
    (inputs : Array Input) (checked : CheckedQuery config.search) :
    NLP (Array (Analysis (Execution config))) :=
  match minWork with
  | none =>
      traverseArrayWeightedIndexed inputs Input.work fun index input ↦
        queryGraphCheckedAt s!"dependency graph query input {index}" config input checked
  | some minimum =>
      traverseArrayWeightedIndexedWithMinWeight minimum inputs Input.work fun index input ↦
        queryGraphCheckedAt s!"dependency graph query input {index}" config input checked

/-- Compile and query a batch with a query whose bounded preflight already succeeded. -/
private def queryGraphsManyCheckedCore (minWork : Option Nat) (config : ExecutionConfig)
    (inputs : Array Input) (checked : CheckedQuery config.search) :
    NLP (Array (Analysis (Execution config))) := do
  checkCancelled
  validateBatchInputs inputs
  queryGraphsManyPreparedCore minWork config inputs checked

/--
Compile and query graphs with bounded work-weighted concurrency and stable input order.

Common query shape is captured once. Cancellation is checked after that pure preflight and before
its outcome is classified; every worker then shares the same protected checked query.
-/
private def queryGraphsManyCore (minWork : Option Nat) (config : ExecutionConfig)
    (inputs : Array Input) (query : Query) :
    NLP (Array (Analysis (Execution config))) := do
  checkCancelled
  validateBatchInputs inputs
  let checkedOutcome := query.checkWith config.search
  checkCancelled
  match checkedOutcome with
  | .error cause =>
      match classifySearchError cause with
      | .inl reason => return Array.replicate inputs.size (.skipped reason)
      | .inr malformed =>
          throw <| .invalidInput "dependency graph query pattern" malformed.detail
  | .ok checked => queryGraphsManyPreparedCore minWork config inputs checked

/-- Run a checked query batch with an explicit aggregate index-work scheduling grain. -/
@[inline] def queryGraphsManyCheckedWithMinWork (minWork : Nat)
    (config : ExecutionConfig) (inputs : Array Input)
    (checked : CheckedQuery config.search) :
    NLP (Array (Analysis (Execution config))) :=
  queryGraphsManyCheckedCore (some minWork) config inputs checked

/-- Run one shared checked query with weighted concurrency and stable output order. -/
@[inline] def queryGraphsManyCheckedWith (config : ExecutionConfig) (inputs : Array Input)
    (checked : CheckedQuery config.search) :
    NLP (Array (Analysis (Execution config))) :=
  queryGraphsManyCheckedCore none config inputs checked

/-- Query graphs with an explicit minimum aggregate index-work scheduling grain. -/
@[inline] def queryGraphsManyWithMinWork (minWork : Nat) (config : ExecutionConfig)
    (inputs : Array Input) (query : Query) :
    NLP (Array (Analysis (Execution config))) :=
  queryGraphsManyCore (some minWork) config inputs query

/-- Query graphs with runtime-weighted concurrency and stable input order. -/
@[inline] def queryGraphsManyWith (config : ExecutionConfig) (inputs : Array Input)
    (query : Query) : NLP (Array (Analysis (Execution config))) :=
  queryGraphsManyCore none config inputs query

/-- Query a graph batch under production policies with deterministic stable output order. -/
@[inline] def queryGraphsMany (inputs : Array Input) (query : Query) :
    NLP (Array (Analysis (Execution {}))) :=
  queryGraphsManyWith {} inputs query

end Nlp.NLP
