import Nlp.Pattern.Tree
import Nlp.Pipeline.Annotate

/-!
# Functional and effectful typed tree queries

The pure boundary builds one checked arena, compiles one typed query, and returns a result whose
type retains the exact query and search policy.  The preferred `NLP` boundary adds cancellation,
runtime yield-length policy, typed resource outcomes, and stable ordered parallel batches.
-/

namespace Nlp.Pattern.TreeQuery

open Nlp.Syntax

/-- Constant-stack work item for source-tree scheduling estimates. -/
private inductive SourceWorkFrame where
  | visit (tree : NamedTree)
  | siblings (trees : Array NamedTree) (next : Nat)
  deriving Inhabited

/--
Deterministic source scheduling weight from constructors and retained UTF-8 label bytes.

The explicit sibling cursor keeps auxiliary storage proportional to tree depth rather than the
width of a branch.
-/
def sourceWork (source : NamedTree) : Nat := Id.run do
  let mut total := 0
  let mut stack : Array SourceWorkFrame := #[.visit source]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .visit (.leaf form) => total := total + form.utf8ByteSize + 1
    | .visit (.node category first rest) =>
        total := total + category.utf8ByteSize + 1
        unless rest.isEmpty do stack := stack.push (.siblings rest 0)
        stack := stack.push (.visit first)
    | .siblings trees next =>
        if next < trees.size then
          stack := stack.push (.siblings trees (next + 1))
          stack := stack.push (.visit trees[next]!)
  return total

/-- A failure from one complete pure tree-query execution. -/
inductive ExecutionError where
  /-- The source tree could not be flattened within the arena policy. -/
  | arena (cause : TreeArenaError)
  /-- The typed query could not be compiled within the syntax policy. -/
  | compile (cause : CompileError)
  /-- The checked arena could not be searched within the evaluation policy. -/
  | search (cause : SearchError)
  deriving Repr, DecidableEq

/--
One source tree, its checked arena witness, the exact compiled query, and certified matches.

The existential source field lets arrays retain results for differently shaped trees without
erasing the query or search-policy indices from each result.
-/
structure Execution (query : Query) (config : SearchConfig) where
  /-- Exact source tree supplied by the caller. -/
  source : NamedTree
  /-- Checked arena retaining proof of correspondence with `source`. -/
  built : TreeArenaBuild source
  /-- Checked postfix program indexed by the exact caller query. -/
  compiled : Compiled query
  /-- Proof-carrying matches over the checked arena. -/
  result : Result built.arena query config

namespace Execution

/-- Matching preorder node identifiers in deterministic source order. -/
@[inline] def nodes (execution : Execution query config) : Array TreeNodeId :=
  execution.result.nodes

/-- Number of retained matching anchors. -/
@[inline] def size (execution : Execution query config) : Nat := execution.result.items.size

/-- Exact terminal yield length of the checked source tree. -/
@[inline] def tokenCount (execution : Execution query config) : Nat :=
  execution.built.arena.leafCount

end Execution

/-- Execute a precompiled query against one source tree through the complete pure boundary. -/
def executeCompiledWith (arenaConfig : TreeArenaConfig) (searchConfig : SearchConfig)
    (compiled : Compiled query) (source : NamedTree) :
    Except ExecutionError (Execution query searchConfig) := do
  let built ← (TreeArena.buildNamedTreeWith arenaConfig source).mapError .arena
  let result ← (findAllWith built.arena searchConfig compiled).mapError .search
  return ⟨source, built, compiled, result⟩

/-- Build, compile, and execute one typed query through the complete pure boundary. -/
def executeWith (arenaConfig : TreeArenaConfig) (compileConfig : CompileConfig)
    (searchConfig : SearchConfig) (query : Query) (source : NamedTree) :
    Except ExecutionError (Execution query searchConfig) := do
  let compiled ← (compileWith compileConfig query).mapError .compile
  executeCompiledWith arenaConfig searchConfig compiled source

/-- Execute one typed tree query under all production policies. -/
@[inline] def execute (query : Query) (source : NamedTree) :
    Except ExecutionError (Execution query {}) :=
  executeWith {} {} {} query source

end Nlp.Pattern.TreeQuery

namespace Nlp.NLP

open Pattern.TreeQuery Syntax

/-- Stable location used for typed tree-query failures. -/
private def treeQueryLocation : String := "typed constituency tree query"

/-- Translate a standalone caller query compilation failure at the effect boundary. -/
private def treeCompileFail : CompileError → Fail
  | .patternNodeBudget required limit =>
      .invalidConfig <|
        s!"tree query requires {required} constructors; configured limit is {limit}"
  | .textBudget required limit =>
      .invalidConfig <|
        s!"tree query retains {required} UTF-8 bytes; configured limit is {limit}"
  | .inconsistentProgram =>
      .modelCorrupt treeQueryLocation "the checked postfix compiler produced an invalid program"

/-- Resource class of one valid typed query that exceeds its selected compilation policy. -/
private def treeCompileSkipReason? : CompileError → Option SkipReason
  | .patternNodeBudget required limit => some (.workLimit required limit)
  | .textBudget required limit => some (.byteLimit required limit)
  | .inconsistentProgram => none

/-- Translate an impossible checked-arena failure without misclassifying a resource limit. -/
private def treeArenaInvariantFail (cause : TreeArenaError) : Fail :=
  .modelCorrupt "checked tree arena" s!"arena construction invariant failed: {repr cause}"

/-- Translate an impossible checked-query failure without hiding its invariant class. -/
private def treeSearchInvariantFail (cause : SearchError) : Fail :=
  .modelCorrupt treeQueryLocation s!"query evaluation invariant failed: {repr cause}"

/-- Compile one typed tree query with cancellation around the bounded pure kernel. -/
def compileTreeQueryWith (config : CompileConfig) (query : Query) :
    NLP (Compiled query) := do
  checkCancelled
  let compiled := compileWith config query
  checkCancelled
  match compiled with
  | .ok value => return value
  | .error cause => throw <| treeCompileFail cause

/-- Compile one typed tree query under the production syntax policy. -/
@[inline] def compileTreeQuery (query : Query) : NLP (Compiled query) :=
  compileTreeQueryWith {} query

/-- Compile for an analysis call, retaining resource exhaustion as typed outcome data. -/
private def compileTreeQueryAnalysisWith (config : CompileConfig) (query : Query) :
    NLP (Analysis (Compiled query)) := do
  checkCancelled
  let compiled := compileWith config query
  checkCancelled
  match compiled with
  | .ok value => return .ok value
  | .error cause =>
      match treeCompileSkipReason? cause with
      | some reason => return .skipped reason
      | none => throw <| treeCompileFail cause

/-- Work item for a bounded, cancellation-aware source-yield preflight. -/
private inductive TreeLengthFrame where
  | visit (tree : NamedTree)
  | siblings (trees : Array NamedTree) (next : Nat)
  deriving Inhabited

/--
Count source terminals only through the first unit beyond `limit` without arena allocation.

Cancellation is checked every 1,024 visited frames and again before returning. Auxiliary storage
is proportional to tree depth, including for a branch with hostile fanout.
-/
private def boundedTreeTokenCount (limit : Nat) (source : NamedTree) : NLP Nat := do
  let mut tokens := 0
  let mut visited := 0
  let mut stack : Array TreeLengthFrame := #[.visit source]
  while !stack.isEmpty && tokens ≤ limit do
    if visited % 1024 = 0 then checkCancelled
    visited := visited + 1
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .visit (.leaf _) => tokens := tokens + 1
    | .visit (.node _ first rest) =>
        unless rest.isEmpty do stack := stack.push (.siblings rest 0)
        stack := stack.push (.visit first)
    | .siblings trees next =>
        if next < trees.size then
          stack := stack.push (.siblings trees (next + 1))
          stack := stack.push (.visit trees[next]!)
  checkCancelled
  return tokens

/-- Execute one already-compiled query with runtime policy and typed resource outcomes. -/
def matchTreeCompiledWith (arenaConfig : TreeArenaConfig) (searchConfig : SearchConfig)
    (compiled : Compiled query) (source : NamedTree) :
    NLP (Analysis (Execution query searchConfig)) := do
  checkCancelled
  let runtime := (← read).config
  let tokens ← boundedTreeTokenCount runtime.maxLen source
  if runtime.maxLen < tokens then return .skipped (.tooLong tokens runtime.maxLen)
  let builtOutcome := TreeArena.buildNamedTreeWith arenaConfig source
  checkCancelled
  let built ←
    match builtOutcome with
    | .ok value => pure value
    | .error (.nodeBudget required limit) =>
        return .skipped (.workLimit required limit)
    | .error (.edgeBudget required limit) =>
        return .skipped (.workLimit required limit)
    | .error (.textBudget required limit) =>
        return .skipped (.byteLimit required limit)
    | .error cause => throw <| treeArenaInvariantFail cause
  let searched := findAllWith built.arena searchConfig compiled
  checkCancelled
  match searched with
  | .ok result => return .ok ⟨source, built, compiled, result⟩
  | .error (.workBudget required limit) =>
      return .skipped (.workLimit required limit)
  | .error (.pathBudget required limit) =>
      return .skipped (.workLimit required limit)
  | .error (.comparedByteBudget required limit) =>
      return .skipped (.byteLimit required limit)
  | .error (.matchBudget required limit) =>
      return .skipped (.candidateLimit required limit)
  | .error cause => throw <| treeSearchInvariantFail cause

/-- Compile and execute one typed tree query with explicit bounded policies. -/
def matchTreeWith (arenaConfig : TreeArenaConfig) (compileConfig : CompileConfig)
    (searchConfig : SearchConfig) (query : Query) (source : NamedTree) :
    NLP (Analysis (Execution query searchConfig)) := do
  match ← compileTreeQueryAnalysisWith compileConfig query with
  | .ok compiled => matchTreeCompiledWith arenaConfig searchConfig compiled source
  | .skipped reason => return .skipped reason
  | .noAnalysis => return .noAnalysis

/-- Compile and execute one typed tree query under all production policies. -/
@[inline] def matchTree (query : Query) (source : NamedTree) :
    NLP (Analysis (Execution query {})) :=
  matchTreeWith {} {} {} query source

/--
Compile once and query trees in stable input order with an explicit minimum parallel grain.
-/
def matchTreesWithMinGrain (minGrain : Nat) (arenaConfig : TreeArenaConfig)
    (compileConfig : CompileConfig) (searchConfig : SearchConfig) (query : Query)
    (sources : Array NamedTree) : NLP (Array (Analysis (Execution query searchConfig))) := do
  match ← compileTreeQueryAnalysisWith compileConfig query with
  | .ok compiled =>
      traverseArrayWithGrain minGrain sources fun source ↦
        matchTreeCompiledWith arenaConfig searchConfig compiled source
  | .skipped reason => return Array.replicate sources.size (.skipped reason)
  | .noAnalysis => return Array.replicate sources.size .noAnalysis

/--
Compile once and query trees in stable source-work order with an explicit minimum work grain.
-/
def matchTreesWithMinWork (minWork : Nat) (arenaConfig : TreeArenaConfig)
    (compileConfig : CompileConfig) (searchConfig : SearchConfig) (query : Query)
    (sources : Array NamedTree) : NLP (Array (Analysis (Execution query searchConfig))) := do
  match ← compileTreeQueryAnalysisWith compileConfig query with
  | .ok compiled =>
      traverseArrayWeightedWithMinWeight minWork sources Pattern.TreeQuery.sourceWork fun source ↦
        matchTreeCompiledWith arenaConfig searchConfig compiled source
  | .skipped reason => return Array.replicate sources.size (.skipped reason)
  | .noAnalysis => return Array.replicate sources.size .noAnalysis

/-- Compile once and query trees in stable input order with runtime parallel policy. -/
def matchTreesWith (arenaConfig : TreeArenaConfig) (compileConfig : CompileConfig)
    (searchConfig : SearchConfig) (query : Query) (sources : Array NamedTree) :
    NLP (Array (Analysis (Execution query searchConfig))) := do
  match ← compileTreeQueryAnalysisWith compileConfig query with
  | .ok compiled =>
      traverseArrayWeighted sources Pattern.TreeQuery.sourceWork fun source ↦
        matchTreeCompiledWith arenaConfig searchConfig compiled source
  | .skipped reason => return Array.replicate sources.size (.skipped reason)
  | .noAnalysis => return Array.replicate sources.size .noAnalysis

/-- Compile once and query trees under production policies with stable ordered parallelism. -/
@[inline] def matchTrees (query : Query) (sources : Array NamedTree) :
    NLP (Array (Analysis (Execution query {}))) :=
  matchTreesWith {} {} {} query sources

end Nlp.NLP
