import Nlp.Syntax.TreeArena

/-!
# Bounded typed tree patterns

This module provides a regular, binding-free Tregex fragment over checked constituency-tree
arenas. Patterns compile iteratively to a private postfix program. Evaluation is a bounded dynamic
program: every pattern-node/tree-node cell is computed once, and indexed relation operators avoid
recursive tree walks and repeated descendant or precedence scans.
-/

namespace Nlp.Pattern.TreeQuery

open Nlp Nlp.Syntax

/-- A supported relation from the current anchor to a target tree node. -/
inductive Relation where
  | child
  | descendant
  | parent
  | leftSibling
  | rightSibling
  | sibling
  | precedes
  | follows
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Typed regular tree-query syntax with exact labels and boolean composition. -/
inductive Query where
  | any
  | label (value : String)
  | both (left right : Query)
  | either (left right : Query)
  | negate (body : Query)
  | related (relation : Relation) (target : Query)
  deriving Repr, DecidableEq, Inhabited

namespace Query

/-- Require an immediate child satisfying `target`. -/
@[inline] def child (target : Query) : Query := .related .child target

/-- Require a strict descendant satisfying `target`. -/
@[inline] def descendant (target : Query) : Query := .related .descendant target

/-- Require the immediate parent to satisfy `target`. -/
@[inline] def parent (target : Query) : Query := .related .parent target

/-- Require the immediate left sibling to satisfy `target`. -/
@[inline] def leftSibling (target : Query) : Query := .related .leftSibling target

/-- Require the immediate right sibling to satisfy `target`. -/
@[inline] def rightSibling (target : Query) : Query := .related .rightSibling target

/-- Require any distinct sibling to satisfy `target`. -/
@[inline] def sibling (target : Query) : Query := .related .sibling target

/-- Require a nonoverlapping following node satisfying `target`. -/
@[inline] def precedes (target : Query) : Query := .related .precedes target

/-- Require a nonoverlapping preceding node satisfying `target`. -/
@[inline] def follows (target : Query) : Query := .related .follows target

end Query

/-- Whether one caller-supplied node identifier belongs to an arena. -/
def ValidNode (arena : TreeArena) (node : TreeNodeId) : Prop :=
  arena.nodeAt? node = some node

/-- Propositional meaning of one supported structural relation. -/
def Related (arena : TreeArena) (relation : Relation)
    (anchor target : TreeNodeId) : Prop :=
  ValidNode arena anchor ∧ ValidNode arena target ∧
    match relation with
    | .child => target ∈ (arena.childrenOf? anchor).getD #[]
    | .descendant =>
        ∃ stop, arena.preorderSpan? anchor = some (anchor, stop) ∧
          anchor < target ∧ target < stop
    | .parent => arena.parent? anchor = some target
    | .leftSibling => arena.leftSibling? anchor = some target
    | .rightSibling => arena.rightSibling? anchor = some target
    | .sibling =>
        target ≠ anchor ∧ ∃ parent,
          arena.parent? anchor = some parent ∧ arena.parent? target = some parent
    | .precedes =>
        ∃ anchorStart anchorStop targetStart targetStop,
          arena.yieldSpan? anchor = some (anchorStart, anchorStop) ∧
          arena.yieldSpan? target = some (targetStart, targetStop) ∧
          anchorStop ≤ targetStart
    | .follows =>
        ∃ anchorStart anchorStop targetStart targetStop,
          arena.yieldSpan? anchor = some (anchorStart, anchorStop) ∧
          arena.yieldSpan? target = some (targetStart, targetStop) ∧
          targetStop ≤ anchorStart

namespace Query

/-- Propositional denotation of one typed tree pattern at an anchor node. -/
def Denotes (arena : TreeArena) (node : TreeNodeId) : Query → Prop
  | .any => ValidNode arena node
  | .label expected => arena.label? node = some expected
  | .both left right => left.Denotes arena node ∧ right.Denotes arena node
  | .either left right => left.Denotes arena node ∨ right.Denotes arena node
  | .negate body => ValidNode arena node ∧ ¬body.Denotes arena node
  | .related relation target =>
      ValidNode arena node ∧ ∃ candidate,
        Related arena relation node candidate ∧ target.Denotes arena candidate

end Query

/-- Exact limits applied while compiling one pattern syntax tree. -/
structure CompileConfig where
  /-- Maximum retained pattern constructors. -/
  maxPatternNodes : Nat := 4_096
  /-- Maximum aggregate UTF-8 bytes across exact labels. -/
  maxTextBytes : Nat := 1_048_576
  deriving Repr, DecidableEq, Inhabited

/-- A deterministic pattern compilation failure. -/
inductive CompileError where
  | patternNodeBudget (required limit : Nat)
  | textBudget (required limit : Nat)
  | inconsistentProgram
  deriving Repr, DecidableEq, Inhabited

/-- Private postfix operation whose operands always precede it. -/
private inductive Op where
  | any
  | label (value : String)
  | both (left right : Nat)
  | either (left right : Nat)
  | negate (body : Nat)
  | related (relation : Relation) (target : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Check every postfix operand and the unique final root. -/
private def checkOps (ops : Array Op) (root : Nat) : Bool := Id.run do
  if ops.isEmpty || root + 1 != ops.size then return false
  for index in [0:ops.size] do
    match ops[index]! with
    | .any | .label _ => pure ()
    | .negate body | .related _ body =>
        unless body < index do return false
    | .both left right | .either left right =>
        unless left < index && right < index do return false
  return true

/-- Independent postfix operation produced directly from the exact source query. -/
private inductive SourceOp where
  | any
  | label (value : String)
  | both (left right : Nat)
  | either (left right : Nat)
  | negate (body : Nat)
  | related (relation : Relation) (target : Nat)
  deriving Inhabited

/-- Independent source-query compilation frame. -/
private inductive SourceFrame where
  | visit (query : Query)
  | emitBoth
  | emitEither
  | emitNegate
  | emitRelated (relation : Relation)
  deriving Inhabited

/-- Compile the exact source query through a second iterative implementation. -/
private def sourceOps (query : Query) : Array SourceOp × Nat := Id.run do
  let mut ops : Array SourceOp := #[]
  let mut values : Array Nat := #[]
  let mut stack : Array SourceFrame := #[.visit query]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .visit current =>
        match current with
        | .any =>
            values := values.push ops.size
            ops := ops.push .any
        | .label value =>
            values := values.push ops.size
            ops := ops.push (.label value)
        | .both left right =>
            stack := stack.push .emitBoth
            stack := stack.push (.visit right)
            stack := stack.push (.visit left)
        | .either left right =>
            stack := stack.push .emitEither
            stack := stack.push (.visit right)
            stack := stack.push (.visit left)
        | .negate body =>
            stack := stack.push .emitNegate
            stack := stack.push (.visit body)
        | .related relation target =>
            stack := stack.push (.emitRelated relation)
            stack := stack.push (.visit target)
    | .emitBoth =>
        let right := values.back!
        values := values.pop
        let left := values.back!
        values := values.pop.push ops.size
        ops := ops.push (.both left right)
    | .emitEither =>
        let right := values.back!
        values := values.pop
        let left := values.back!
        values := values.pop.push ops.size
        ops := ops.push (.either left right)
    | .emitNegate =>
        let body := values.back!
        values := values.pop.push ops.size
        ops := ops.push (.negate body)
    | .emitRelated relation =>
        let target := values.back!
        values := values.pop.push ops.size
        ops := ops.push (.related relation target)
  return (ops, values.back!)

/-- Constructor-protected independent program with erased exact-source provenance. -/
private structure SourceProgram (source : Query) where
  mk ::
  ops : Array SourceOp
  root : Nat
  exact : (ops, root) = sourceOps source

/-- Construct the independent program once from its exact source query. -/
private def compileSourceProgram (source : Query) : SourceProgram source :=
  let built := sourceOps source
  ⟨built.1, built.2, rfl⟩

/-- Constructor-protected postfix form indexed by its exact source query. -/
structure Compiled (source : Query) where
  private mk ::
  private ops : Array Op
  private root : Nat
  private sourceProgram : SourceProgram source
  private checked : checkOps ops root = true

namespace Compiled

/-- Executable well-formedness of a compiled tree pattern. -/
def WF (compiled : Compiled source) : Prop := checkOps compiled.ops compiled.root = true

/-- Every constructible compiled pattern passes the complete postfix checker. -/
theorem wellFormed (compiled : Compiled source) : compiled.WF := compiled.checked

/-- Number of retained pattern constructors. -/
@[inline] def opCount (compiled : Compiled source) : Nat := compiled.ops.size

/-- Exact source query retained by the compiled type index. -/
@[inline] def sourceQuery (_compiled : Compiled source) : Query := source

/-- The exposed source query is definitionally the caller's compiled query. -/
theorem sourceQuery_eq (compiled : Compiled source) : compiled.sourceQuery = source := rfl

/-- The retained independent program was constructed directly from the exact source query. -/
def IndependentWF (compiled : Compiled source) : Prop :=
  (compiled.sourceProgram.ops, compiled.sourceProgram.root) = sourceOps source

/-- Every compiled query retains an exact independent source-program certificate. -/
theorem independentWellFormed (compiled : Compiled source) : compiled.IndependentWF :=
  compiled.sourceProgram.exact

end Compiled

/-- Deferred postfix emission step used by the iterative compiler. -/
private inductive CompileFrame where
  | visit (query : Query)
  | emitBoth
  | emitEither
  | emitNegate
  | emitRelated (relation : Relation)
  deriving Inhabited

/-- Seal a generated postfix program after validating every reference. -/
private def sealCompiled (source : Query) (ops : Array Op) (root : Nat) :
    Except CompileError (Compiled source) :=
  match checked : checkOps ops root with
  | true =>
      let sourceProgram := compileSourceProgram source
      .ok ⟨ops, root, sourceProgram, checked⟩
  | false => .error .inconsistentProgram

/-- Compile a query iteratively under exact syntax-node and lexical-byte caps. -/
def compileWith (config : CompileConfig) (query : Query) :
    Except CompileError (Compiled query) := do
  let mut ops : Array Op := #[]
  let mut values : Array Nat := #[]
  let mut stack : Array CompileFrame := #[.visit query]
  let mut nodes := 0
  let mut textBytes := 0
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .visit current =>
        let requiredNodes := nodes + 1
        if config.maxPatternNodes < requiredNodes then
          throw <| .patternNodeBudget requiredNodes config.maxPatternNodes
        nodes := requiredNodes
        match current with
        | .any =>
            values := values.push ops.size
            ops := ops.push .any
        | .label value =>
            let requiredText := textBytes + value.utf8ByteSize
            if config.maxTextBytes < requiredText then
              throw <| .textBudget requiredText config.maxTextBytes
            textBytes := requiredText
            values := values.push ops.size
            ops := ops.push (.label value)
        | .both left right =>
            stack := stack.push .emitBoth
            stack := stack.push (.visit right)
            stack := stack.push (.visit left)
        | .either left right =>
            stack := stack.push .emitEither
            stack := stack.push (.visit right)
            stack := stack.push (.visit left)
        | .negate body =>
            stack := stack.push .emitNegate
            stack := stack.push (.visit body)
        | .related relation target =>
            stack := stack.push (.emitRelated relation)
            stack := stack.push (.visit target)
    | .emitBoth =>
        let right := values.back!
        values := values.pop
        let left := values.back!
        values := values.pop
        values := values.push ops.size
        ops := ops.push (.both left right)
    | .emitEither =>
        let right := values.back!
        values := values.pop
        let left := values.back!
        values := values.pop
        values := values.push ops.size
        ops := ops.push (.either left right)
    | .emitNegate =>
        let body := values.back!
        values := values.pop
        values := values.push ops.size
        ops := ops.push (.negate body)
    | .emitRelated relation =>
        let target := values.back!
        values := values.pop
        values := values.push ops.size
        ops := ops.push (.related relation target)
  sealCompiled query ops values.back!

/-- Compile a query under production syntax limits. -/
@[inline] def compile (query : Query) : Except CompileError (Compiled query) :=
  compileWith {} query

/-- Exact limits for one compiled tree-pattern search. -/
structure SearchConfig where
  /-- Maximum fixed dynamic-program cells plus independent certificate steps. -/
  maxWork : Nat := 67_108_864
  /-- Maximum indexed relation endpoints inspected across both fixed evaluators. -/
  maxPaths : Nat := 67_108_864
  /-- Maximum conservative UTF-8 bytes presented to exact-label comparisons. -/
  maxComparedBytes : Nat := 4_294_967_296
  /-- Maximum matching preorder anchors retained in the output. -/
  maxMatches : Nat := 1_048_576
  deriving Repr, DecidableEq, Inhabited

/-- Why a bounded tree-pattern search could not complete. -/
inductive SearchError where
  | workBudget (required limit : Nat)
  | pathBudget (required limit : Nat)
  | comparedByteBudget (required limit : Nat)
  | matchBudget (required limit : Nat)
  | inconsistentArena
  | denotationMismatch
  deriving Repr, DecidableEq, Inhabited

/-- Exact fixed work and indexed-path requirements before result retention. -/
structure Requirements where
  /-- Exact cells in both truth tables plus independent source-query compilation steps. -/
  work : Nat
  /-- Exact indexed relationship endpoints inspected across both evaluators. -/
  paths : Nat
  /-- Conservative byte upper bound for all fixed exact-label comparisons. -/
  comparedByteUpperBound : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Exact indexed-endpoint count for one optimized relation column. -/
private def relationPaths (arena : TreeArena) : Relation → Nat
  | .child => arena.edgeCount
  | .descendant => 2 * arena.nodeCount
  | .parent | .leftSibling | .rightSibling => arena.nodeCount
  | .sibling => 2 * arena.nodeCount
  | .precedes | .follows => 2 * arena.nodeCount + arena.leafCount + 1

/-- Exact endpoint count for one independently evaluated source-query relation column. -/
private def sourceRelationPaths (arena : TreeArena) : Relation → Nat
  | .child | .parent | .leftSibling | .rightSibling => arena.nodeCount
  | .descendant | .sibling => 2 * arena.nodeCount
  | .precedes | .follows => 2 * arena.nodeCount + arena.leafCount + 1

/-- Exact fixed evaluator requirements, excluding the data-dependent final match count. -/
def requirements (compiled : Compiled source) (arena : TreeArena) : Requirements :=
  let optimizedPaths := compiled.ops.foldl (fun total op =>
    match op with
    | .related relation _ => total + relationPaths arena relation
    | _ => total) 0
  let independentPaths := compiled.sourceProgram.ops.foldl (fun total op =>
    match op with
    | .related relation _ => total + sourceRelationPaths arena relation
    | _ => total) 0
  let arenaBytes := arena.labelBytes
  let optimizedBytes := compiled.ops.foldl (fun total op =>
    match op with
    | .label expected =>
        total + arenaBytes + arena.nodeCount * expected.utf8ByteSize
    | _ => total) 0
  let independentBytes := compiled.sourceProgram.ops.foldl (fun total op =>
    match op with
    | .label expected =>
        total + arenaBytes + arena.nodeCount * expected.utf8ByteSize
    | _ => total) 0
  let optimizedCells := compiled.opCount * arena.nodeCount
  let independentCells := compiled.sourceProgram.ops.size * arena.nodeCount
  { work := optimizedCells + independentCells + compiled.sourceProgram.ops.size,
    paths := optimizedPaths + independentPaths,
    comparedByteUpperBound := optimizedBytes + independentBytes }

/-- Read one independent source-query truth cell. -/
@[inline] private def sourceTruthAt (table : Array Bool) (nodes op node : Nat) : Bool :=
  table.getD (op * nodes + node) false

/-- Independently evaluate one source-query relation column in linear indexed time. -/
private def sourceRelationRow (arena : TreeArena) (table : Array Bool)
    (target : Nat) : Relation → Array Bool
  | .child => Id.run do
      let mut row := Array.replicate arena.nodeCount false
      for candidate in [0:arena.nodeCount] do
        if sourceTruthAt table arena.nodeCount target candidate then
          match arena.parent? candidate with
          | some parent => row := row.set! parent true
          | none => pure ()
      return row
  | .descendant => Id.run do
      let mut prefixCounts := Array.emptyWithCapacity (arena.nodeCount + 1)
      let mut count := 0
      prefixCounts := prefixCounts.push 0
      for candidate in [0:arena.nodeCount] do
        if sourceTruthAt table arena.nodeCount target candidate then count := count + 1
        prefixCounts := prefixCounts.push count
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for anchor in [0:arena.nodeCount] do
        match arena.preorderSpan? anchor with
        | some (_, stop) =>
            row := row.push (decide (prefixCounts[anchor + 1]! < prefixCounts[stop]!))
        | none => row := row.push false
      return row
  | .parent => Id.run do
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for anchor in [0:arena.nodeCount] do
        row := row.push <| (arena.parent? anchor).any fun parent =>
          sourceTruthAt table arena.nodeCount target parent
      return row
  | .leftSibling => Id.run do
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for anchor in [0:arena.nodeCount] do
        row := row.push <| (arena.leftSibling? anchor).any fun sibling =>
          sourceTruthAt table arena.nodeCount target sibling
      return row
  | .rightSibling => Id.run do
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for anchor in [0:arena.nodeCount] do
        row := row.push <| (arena.rightSibling? anchor).any fun sibling =>
          sourceTruthAt table arena.nodeCount target sibling
      return row
  | .sibling => Id.run do
      let mut counts := Array.replicate arena.nodeCount 0
      for candidate in [0:arena.nodeCount] do
        if sourceTruthAt table arena.nodeCount target candidate then
          match arena.parent? candidate with
          | some parent => counts := counts.set! parent (counts[parent]! + 1)
          | none => pure ()
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for anchor in [0:arena.nodeCount] do
        row := row.push <| match arena.parent? anchor with
          | some parent =>
              let self := if sourceTruthAt table arena.nodeCount target anchor then 1 else 0
              self < counts[parent]!
          | none => false
      return row
  | .precedes => Id.run do
      let slots := arena.leafCount + 1
      let mut starts := Array.replicate slots false
      for candidate in [0:arena.nodeCount] do
        if sourceTruthAt table arena.nodeCount target candidate then
          match arena.yieldSpan? candidate with
          | some (start, _) => starts := starts.set! start true
          | none => pure ()
      let mut suffix := Array.replicate slots false
      let mut found := false
      for cursor in [0:slots] do
        let ordinal := arena.leafCount - cursor
        found := found || starts[ordinal]!
        suffix := suffix.set! ordinal found
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for anchor in [0:arena.nodeCount] do
        row := row.push <| (arena.yieldSpan? anchor).any fun (_, stop) => suffix[stop]!
      return row
  | .follows => Id.run do
      let slots := arena.leafCount + 1
      let mut stops := Array.replicate slots false
      for candidate in [0:arena.nodeCount] do
        if sourceTruthAt table arena.nodeCount target candidate then
          match arena.yieldSpan? candidate with
          | some (_, stop) => stops := stops.set! stop true
          | none => pure ()
      let mut prefixSeen := Array.replicate slots false
      let mut found := false
      for ordinal in [0:slots] do
        found := found || stops[ordinal]!
        prefixSeen := prefixSeen.set! ordinal found
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for anchor in [0:arena.nodeCount] do
        row := row.push <| (arena.yieldSpan? anchor).any fun (start, _) =>
          prefixSeen[start]!
      return row

/-- Evaluate one already-compiled independent source program. -/
private def evalSourceProgram (arena : TreeArena) (program : Array SourceOp × Nat) :
    Array Bool × Nat := Id.run do
  let mut table := Array.emptyWithCapacity (program.1.size * arena.nodeCount)
  for op in program.1 do
    match op with
    | .any =>
        for _ in [0:arena.nodeCount] do table := table.push true
    | .label expected =>
        for node in [0:arena.nodeCount] do
          table := table.push (arena.label? node == some expected)
    | .both left right =>
        for node in [0:arena.nodeCount] do
          table := table.push <|
            sourceTruthAt table arena.nodeCount left node &&
              sourceTruthAt table arena.nodeCount right node
    | .either left right =>
        for node in [0:arena.nodeCount] do
          table := table.push <|
            sourceTruthAt table arena.nodeCount left node ||
              sourceTruthAt table arena.nodeCount right node
    | .negate body =>
        for node in [0:arena.nodeCount] do
          table := table.push (!sourceTruthAt table arena.nodeCount body node)
    | .related relation target =>
        for accepted in sourceRelationRow arena table target relation do
          table := table.push accepted
  return (table, program.2)

/-- Evaluate the exact source query independently as a complete flat truth table. -/
private def sourceTruthTable (arena : TreeArena) (query : Query) : Array Bool × Nat :=
  evalSourceProgram arena (sourceOps query)

/-- Shared independent executable certificate for one exact source query. -/
structure DenotationTable (arena : TreeArena) (query : Query) where
  private mk ::
  private evaluated : Array Bool × Nat
  private exact : evaluated = sourceTruthTable arena query

namespace DenotationTable

/-- Executable source-query acceptance at one caller-selected node. -/
@[inline] def accepts (certificate : DenotationTable arena query) (node : TreeNodeId) : Bool :=
  sourceTruthAt certificate.evaluated.1 arena.nodeCount certificate.evaluated.2 node

/-- The stored table and root are exactly the independent direct-source-query evaluation. -/
def WF (certificate : DenotationTable arena query) : Prop :=
  certificate.evaluated = sourceTruthTable arena query

/-- Every constructible denotation table is exact. -/
theorem wellFormed (certificate : DenotationTable arena query) : certificate.WF :=
  certificate.exact

end DenotationTable

/-- Construct one shared independent denotation table from the exact source query. -/
private def buildDenotationTable (arena : TreeArena) (compiled : Compiled query) :
    DenotationTable arena query :=
  let program := (compiled.sourceProgram.ops, compiled.sourceProgram.root)
  let exact := congrArg (evalSourceProgram arena) compiled.sourceProgram.exact
  ⟨evalSourceProgram arena program, exact⟩

/-- One matching anchor certified against its exact arena and source query. -/
structure Match (arena : TreeArena) (query : Query) (config : SearchConfig) where
  private mk ::
  /-- Matching node identifier. -/
  node : TreeNodeId
  /-- Shared exact source-query truth table. -/
  certificate : DenotationTable arena query
  private valid : arena.nodeAt? node = some node
  private certified : certificate.accepts node = true

namespace Match

/-- Executable semantic well-formedness and shared independent query certificate. -/
def WF {arena : TreeArena} {query : Query} {config : SearchConfig}
    (matched : Match arena query config) : Prop :=
  arena.nodeAt? matched.node = some matched.node ∧
    matched.certificate.WF ∧ matched.certificate.accepts matched.node = true

/-- Every emitted anchor is present and independently accepted by its exact source query. -/
theorem wellFormed {arena : TreeArena} {query : Query} {config : SearchConfig}
    (matched : Match arena query config) : matched.WF :=
  ⟨matched.valid, matched.certificate.wellFormed, matched.certified⟩

end Match

/-- A successful deterministic search indexed by its arena, exact source query, and policy. -/
structure Result (arena : TreeArena) (query : Query) (config : SearchConfig) where
  private mk ::
  /-- Proof-carrying matching anchors in deterministic tree preorder. -/
  items : Array (Match arena query config)
  /-- Exact work for both tables and independent source-query compilation. -/
  work : Nat
  /-- Exact indexed relation-endpoint charge across both evaluators. -/
  paths : Nat
  /-- Exact byte-length sum presented to all fixed exact-label comparisons. -/
  comparedBytes : Nat
  private workBound : work ≤ config.maxWork
  private pathBound : paths ≤ config.maxPaths
  private comparedByteBound : comparedBytes ≤ config.maxComparedBytes
  private matchBound : items.size ≤ config.maxMatches

namespace Result

/-- Successful evaluation stays within its work policy. -/
theorem work_le (result : Result arena query config) : result.work ≤ config.maxWork :=
  result.workBound

/-- Successful relation evaluation stays within its indexed-path policy. -/
theorem paths_le (result : Result arena query config) : result.paths ≤ config.maxPaths :=
  result.pathBound

/-- Successful exact-label evaluation stays within its compared-byte policy. -/
theorem comparedBytes_le (result : Result arena query config) :
    result.comparedBytes ≤ config.maxComparedBytes :=
  result.comparedByteBound

/-- Successful output retention stays within its match policy. -/
theorem size_le (result : Result arena query config) : result.items.size ≤ config.maxMatches :=
  result.matchBound

/-- Erase anchor certificates to plain preorder node identifiers. -/
def nodes (result : Result arena query config) : Array TreeNodeId :=
  result.items.map fun matched => matched.node

end Result

/-- Read one prior postfix truth cell from the flat dynamic-program table. -/
@[inline] private def truthAt (table : Array Bool) (nodes op node : Nat) : Bool :=
  table.getD (op * nodes + node) false

/-- Evaluate one optimized relation column without recursive tree traversal. -/
private def evalRelation (arena : TreeArena) (table : Array Bool)
    (target : Nat) : Relation → Array Bool
  | .child => Id.run do
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        let mut found := false
        match arena.childRange? node with
        | none => pure ()
        | some (start, stop) =>
            for ordinal in [0:stop - start] do
              match arena.childAt? node ordinal with
              | some child => found := found || truthAt table arena.nodeCount target child
              | none => pure ()
        row := row.push found
      return row
  | .descendant => Id.run do
      let mut prefixCounts := Array.emptyWithCapacity (arena.nodeCount + 1)
      let mut count := 0
      prefixCounts := prefixCounts.push 0
      for node in [0:arena.nodeCount] do
        if truthAt table arena.nodeCount target node then count := count + 1
        prefixCounts := prefixCounts.push count
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        match arena.preorderSpan? node with
        | some (_, stop) =>
            row := row.push (decide (prefixCounts[stop]! > prefixCounts[node + 1]!))
        | none => row := row.push false
      return row
  | .parent => Id.run do
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        row := row.push <| match arena.parent? node with
          | some parent => truthAt table arena.nodeCount target parent
          | none => false
      return row
  | .leftSibling => Id.run do
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        row := row.push <| match arena.leftSibling? node with
          | some sibling => truthAt table arena.nodeCount target sibling
          | none => false
      return row
  | .rightSibling => Id.run do
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        row := row.push <| match arena.rightSibling? node with
          | some sibling => truthAt table arena.nodeCount target sibling
          | none => false
      return row
  | .sibling => Id.run do
      let mut counts := Array.replicate arena.nodeCount 0
      for candidate in [0:arena.nodeCount] do
        match arena.parent? candidate with
        | some parent =>
            if truthAt table arena.nodeCount target candidate then
              counts := counts.set! parent (counts[parent]! + 1)
        | none => pure ()
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        row := row.push <| match arena.parent? node with
          | some parent =>
              let self := if truthAt table arena.nodeCount target node then 1 else 0
              self < counts[parent]!
          | none => false
      return row
  | .precedes => Id.run do
      let slots := arena.leafCount + 1
      let mut atStart := Array.replicate slots false
      for candidate in [0:arena.nodeCount] do
        if truthAt table arena.nodeCount target candidate then
          match arena.yieldSpan? candidate with
          | some (start, _) => atStart := atStart.set! start true
          | none => pure ()
      let mut suffix := Array.replicate slots false
      let mut seen := false
      for cursor in [0:slots] do
        let index := arena.leafCount - cursor
        seen := seen || atStart[index]!
        suffix := suffix.set! index seen
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        row := row.push <| match arena.yieldSpan? node with
          | some (_, stop) => suffix[stop]!
          | none => false
      return row
  | .follows => Id.run do
      let slots := arena.leafCount + 1
      let mut atStop := Array.replicate slots false
      for candidate in [0:arena.nodeCount] do
        if truthAt table arena.nodeCount target candidate then
          match arena.yieldSpan? candidate with
          | some (_, stop) => atStop := atStop.set! stop true
          | none => pure ()
      let mut prefixSeen := Array.replicate slots false
      let mut seen := false
      for index in [0:slots] do
        seen := seen || atStop[index]!
        prefixSeen := prefixSeen.set! index seen
      let mut row := Array.emptyWithCapacity arena.nodeCount
      for node in [0:arena.nodeCount] do
        row := row.push <| match arena.yieldSpan? node with
          | some (start, _) => prefixSeen[start]!
          | none => false
      return row

/-- Seal one matching node against the shared independent source-query truth table. -/
private def sealMatch (arena : TreeArena) (config : SearchConfig)
    (certificate : DenotationTable arena query) (node : TreeNodeId) :
    Except SearchError (Match arena query config) := do
  if valid : arena.nodeAt? node = some node then
    if certified : certificate.accepts node = true then
      return ⟨node, certificate, valid, certified⟩
    else
      throw .denotationMismatch
  else
    throw .inconsistentArena

/-- Find all matching anchors in deterministic preorder under exact resource budgets. -/
def findAllWith (arena : TreeArena) (config : SearchConfig)
    (compiled : Compiled source) : Except SearchError (Result arena source config) := do
  let needed := requirements compiled arena
  if config.maxWork < needed.work then
    throw <| .workBudget needed.work config.maxWork
  if config.maxPaths < needed.paths then
    throw <| .pathBudget needed.paths config.maxPaths
  if config.maxComparedBytes < needed.comparedByteUpperBound then
    throw <| .comparedByteBudget needed.comparedByteUpperBound config.maxComparedBytes
  let mut table := Array.emptyWithCapacity (compiled.opCount * arena.nodeCount)
  for op in compiled.ops do
    match op with
    | .any =>
        for _ in [0:arena.nodeCount] do table := table.push true
    | .label expected =>
        for node in [0:arena.nodeCount] do
          table := table.push (arena.label? node == some expected)
    | .both left right =>
        for node in [0:arena.nodeCount] do
          table := table.push <|
            truthAt table arena.nodeCount left node && truthAt table arena.nodeCount right node
    | .either left right =>
        for node in [0:arena.nodeCount] do
          table := table.push <|
            truthAt table arena.nodeCount left node || truthAt table arena.nodeCount right node
    | .negate body =>
        for node in [0:arena.nodeCount] do
          table := table.push (!truthAt table arena.nodeCount body node)
    | .related relation target =>
        for value in evalRelation arena table target relation do
          table := table.push value
  let certificate := buildDenotationTable arena compiled
  let mut items := Array.empty
  for node in [0:arena.nodeCount] do
    if truthAt table arena.nodeCount compiled.root node then
      let required := items.size + 1
      if config.maxMatches < required then
        throw <| .matchBudget required config.maxMatches
      items := items.push (← sealMatch arena config certificate node)
  if workBound : needed.work ≤ config.maxWork then
    if pathBound : needed.paths ≤ config.maxPaths then
      if comparedByteBound : needed.comparedByteUpperBound ≤ config.maxComparedBytes then
        if matchBound : items.size ≤ config.maxMatches then
          return ⟨items, needed.work, needed.paths, needed.comparedByteUpperBound,
            workBound, pathBound, comparedByteBound, matchBound⟩
        else
          throw <| .matchBudget items.size config.maxMatches
      else
        throw <| .comparedByteBudget needed.comparedByteUpperBound
          config.maxComparedBytes
    else
      throw <| .pathBudget needed.paths config.maxPaths
  else
    throw <| .workBudget needed.work config.maxWork

/-- Find all matching anchors under production budgets. -/
@[inline] def findAll (arena : TreeArena) (compiled : Compiled source) :
    Except SearchError (Result arena source {}) :=
  findAllWith arena {} compiled

/-- Compile and evaluate one typed query under production budgets. -/
def run (arena : TreeArena) (query : Query) :
    Except (CompileError ⊕ SearchError) (Result arena query {}) := do
  let compiled ← (compile query).mapError Sum.inl
  (findAll arena compiled).mapError Sum.inr

end Nlp.Pattern.TreeQuery
