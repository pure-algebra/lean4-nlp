import Nlp.Core.Data.DependencyGraph
import Nlp.Pattern.Token

/-!
# Typed dependency-graph patterns

This module builds a checked outgoing index beside the canonical incoming CSR columns of an
enhanced dependency graph. Queries remain a small typed algebra: node predicates, boolean
composition, direct labeled edges, and named-node equality. The evaluator is explicitly bounded
and visits nodes and edges in canonical order.
-/

namespace Nlp.Pattern.GraphQuery

open Nlp.Dependency

/-- Optional token columns aligned with one stored dependency-graph node. -/
structure NodeAttributes where
  /-- Source-preserving token form, when the node corresponds to an annotated token. -/
  form : Option String := none
  /-- Part-of-speech tag, when available. -/
  pos : Option String := none
  /-- Lemma, when available. -/
  lemma : Option String := none
  /-- Existing named-entity class, when available. -/
  ner : Option String := none
  deriving Repr, DecidableEq, Inhabited

namespace NodeAttributes

/-- Exact UTF-8 bytes retained by one optional node-attribute record. -/
def lexicalBytes (attributes : NodeAttributes) : Nat :=
  (attributes.form.map String.utf8ByteSize).getD 0
    + (attributes.pos.map String.utf8ByteSize).getD 0
    + (attributes.lemma.map String.utf8ByteSize).getD 0
    + (attributes.ner.map String.utf8ByteSize).getD 0

end NodeAttributes

/-- Exact allocation limits for compiling a dual dependency-graph index. -/
structure IndexConfig where
  /-- Maximum number of stored non-root graph nodes. -/
  maxNodes : Nat := 1_048_576
  /-- Maximum number of directed labeled graph edges. -/
  maxEdges : Nat := 4_194_304
  /-- Maximum UTF-8 bytes retained by relations and optional node attributes. -/
  maxLexicalBytes : Nat := 67_108_864
  /--
  Maximum node coordinate; the default fixes coordinates to 32 bits. Raising it explicitly
  widens the arbitrary-precision comparison-cost envelope.
  -/
  maxCoordinate : Nat := 4_294_967_295
  deriving Repr, DecidableEq, Inhabited

/-- Why a checked graph index could not be compiled. -/
inductive IndexError where
  /-- The graph and attribute columns are not aligned. -/
  | attributeCount (expected found : Nat)
  /-- The stored node count exceeds policy. -/
  | nodeBudget (required limit : Nat)
  /-- The stored edge count exceeds policy. -/
  | edgeBudget (required limit : Nat)
  /-- Retained relation and attribute text exceeds policy. -/
  | lexicalByteBudget (required limit : Nat)
  /-- A node coordinate exceeds the bounded-width comparison policy. -/
  | coordinateBudget (required limit : Nat)
  /-- A checked graph unexpectedly exposed a head outside its node set. -/
  | missingHead (edge : Nat) (head : NodeId)
  /-- Compiler output failed its complete dual-index consistency check. -/
  | inconsistentStorage
  deriving Repr, DecidableEq, Inhabited

/-- Return a queryable node identifier from its root-inclusive dense ordinal. -/
@[inline] private def nodeAtDense? (graph : Dependency.Graph String)
    (dense : Nat) : Option NodeId :=
  if dense = 0 then some .root else graph.nodes[dense - 1]?

/-- Exact relation and node-attribute bytes retained by an index. -/
def requiredLexicalBytes (graph : Dependency.Graph String)
    (attributes : Array NodeAttributes) : Nat :=
  let relationBytes := graph.relations.foldl
    (fun total relation ↦ total + relation.utf8ByteSize) 0
  attributes.foldl (fun total node ↦ total + node.lexicalBytes) relationBytes

/-- Largest natural-number coordinate occurring in one node identifier. -/
@[inline] private def nodeCoordinate : NodeId → Nat
  | .root => 0
  | .word index => index
  | .empty anchor copy | .copy anchor copy => max anchor copy

/-- Largest coordinate retained by graph node and head columns. -/
def requiredCoordinate (graph : Dependency.Graph String) : Nat :=
  let nodeMaximum := graph.nodes.foldl (fun found node ↦ max found (nodeCoordinate node)) 0
  graph.heads.foldl (fun found node ↦ max found (nodeCoordinate node)) nodeMaximum

/-- Check every parallel dense-edge column and the outgoing edge permutation. -/
private def checkStorage (graph : Dependency.Graph String)
    (attributes : Array NodeAttributes) (lexicalBytes coordinateMaximum : Nat)
    (headDense dependentDense : Array Nat)
    (outgoingOffsets outgoingEdges : Array Nat) : Bool := Id.run do
  let nodes := graph.nodeCount
  let edges := graph.edgeCount
  let denseNodes := nodes + 1
  unless attributes.size = nodes do return false
  unless lexicalBytes = requiredLexicalBytes graph attributes do return false
  unless coordinateMaximum = requiredCoordinate graph do return false
  unless headDense.size = edges && dependentDense.size = edges do return false
  unless outgoingOffsets.size = denseNodes + 1 do return false
  unless outgoingEdges.size = edges do return false
  unless outgoingOffsets[0]? = some 0 do return false
  for row in [0:nodes] do
    let start := graph.offsets[row]!
    let stop := graph.offsets[row + 1]!
    for edge in [start:stop] do
      unless dependentDense[edge]? = some (row + 1) do return false
      let headIndex := headDense[edge]!
      unless nodeAtDense? graph headIndex = graph.heads[edge]? do return false
  let mut seen := Array.replicate edges false
  for source in [0:denseNodes] do
    let start := outgoingOffsets[source]!
    let stop := outgoingOffsets[source + 1]!
    unless start ≤ stop && stop ≤ edges do return false
    let mut previous : Option Nat := none
    for cursor in [start:stop] do
      let edge := outgoingEdges[cursor]!
      unless edge < edges do return false
      unless headDense[edge]? = some source do return false
      if seen[edge]! then return false
      seen := seen.set! edge true
      match previous with
      | some prior => unless prior < edge do return false
      | none => pure ()
      previous := some edge
  unless outgoingOffsets.back? = some edges do return false
  return seen.all id

/-- A constructor-protected root-inclusive dual index over a checked dependency graph. -/
structure Index where
  private mk ::
  /-- Source checked graph; its incoming CSR columns are reused without copying. -/
  graph : Dependency.Graph String
  /-- Optional attributes aligned with `graph.nodes`. -/
  attributes : Array NodeAttributes
  /-- Checked relation and node-attribute UTF-8 bytes retained by this index. -/
  private storedLexicalBytes : Nat
  /-- Checked largest coordinate bounding every canonical node comparison. -/
  private storedCoordinateMaximum : Nat
  /-- Root-inclusive dense head ordinal for every original edge. -/
  private headDense : Array Nat
  /-- Root-inclusive dense dependent ordinal for every original edge. -/
  private dependentDense : Array Nat
  /-- CSR boundaries for outgoing edge ordinals, including the artificial root row. -/
  private outgoingOffsets : Array Nat
  /-- Original edge ordinals grouped by head and ordered by dependent and relation. -/
  private outgoingEdges : Array Nat
  private checked :
    checkStorage graph attributes storedLexicalBytes storedCoordinateMaximum headDense
      dependentDense outgoingOffsets outgoingEdges = true

namespace Index

/-- Executable storage invariant for a compiled graph index. -/
def WF (index : Index) : Prop :=
  checkStorage index.graph index.attributes index.storedLexicalBytes
    index.storedCoordinateMaximum index.headDense index.dependentDense index.outgoingOffsets
    index.outgoingEdges = true

/-- Every public graph index passes its complete dual-storage checker. -/
theorem wellFormed (index : Index) : index.WF := index.checked

/-- Number of queryable nodes, including the artificial root. -/
@[inline] def nodeCount (index : Index) : Nat := index.graph.nodeCount + 1

/-- Number of directed labeled edges in both adjacency views. -/
@[inline] def edgeCount (index : Index) : Nat := index.graph.edgeCount

/-- Checked UTF-8 bytes retained by relation and optional node-attribute columns. -/
@[inline] def lexicalBytes (index : Index) : Nat := index.storedLexicalBytes

/-- Checked largest natural coordinate used by canonical node comparisons. -/
@[inline] def coordinateMaximum (index : Index) : Nat := index.storedCoordinateMaximum

/-- Read one root-inclusive dense node ordinal. -/
@[inline] def nodeAt? (index : Index) (dense : Nat) : Option NodeId :=
  nodeAtDense? index.graph dense

private structure DenseLookup where
  dense : Option Nat
  comparisons : Nat

/-- Binary-search one non-root canonical node while counting exact coordinate comparisons. -/
private def denseLookupAux (nodes : Array NodeId) (target : NodeId) :
    Nat → Nat → Nat → DenseLookup
  | 0, _, _ => ⟨none, 0⟩
  | fuel + 1, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        match nodes[middle]? with
        | none => ⟨none, 0⟩
        | some found =>
            match target.compare found with
            | .eq => ⟨some (middle + 1), 1⟩
            | .lt =>
                let next := denseLookupAux nodes target fuel lower middle
                { next with comparisons := next.comparisons + 1 }
            | .gt =>
                let next := denseLookupAux nodes target fuel (middle + 1) upper
                { next with comparisons := next.comparisons + 1 }
      else ⟨none, 0⟩

/-- Root/ordinary-word fast lookup with bounded binary fallback and exact comparison count. -/
@[inline] private def denseLookup (graph : Dependency.Graph String)
    (node : NodeId) : DenseLookup :=
  match node with
  | .root => ⟨some 0, 1⟩
  | .word index =>
      match graph.nodes[index - 1]? with
      | some found =>
          if node.compare found == .eq then
            ⟨some index, 2⟩
          else
            let searched :=
              denseLookupAux graph.nodes node (graph.nodeCount + 1) 0 graph.nodeCount
            { searched with comparisons := searched.comparisons + 2 }
      | none =>
          let searched :=
            denseLookupAux graph.nodes node (graph.nodeCount + 1) 0 graph.nodeCount
          { searched with comparisons := searched.comparisons + 1 }
  | .empty .. | .copy .. =>
      let searched := denseLookupAux graph.nodes node (graph.nodeCount + 1) 0 graph.nodeCount
      { searched with comparisons := searched.comparisons + 1 }

/-- Find one queryable node in logarithmically many bounded-coordinate comparisons. -/
def denseOf? (index : Index) (node : NodeId) : Option Nat :=
  (denseLookup index.graph node).dense

/-- Read optional token attributes for one root-inclusive dense node. -/
@[inline] def attributesAt? (index : Index) (dense : Nat) : Option NodeAttributes :=
  if dense = 0 then none else index.attributes[dense - 1]?

/-- Seal compiler output only after the complete executable index check succeeds. -/
private def sealIndex (graph : Dependency.Graph String) (attributes : Array NodeAttributes)
    (lexicalBytes coordinateMaximum : Nat)
    (headDense dependentDense outgoingOffsets outgoingEdges : Array Nat) :
    Except IndexError Index :=
  match checked : checkStorage graph attributes lexicalBytes coordinateMaximum headDense
      dependentDense outgoingOffsets outgoingEdges with
  | true =>
      .ok ⟨graph, attributes, lexicalBytes, coordinateMaximum, headDense, dependentDense,
        outgoingOffsets, outgoingEdges, checked⟩
  | false => .error .inconsistentStorage

/-- Compile a checked graph to dual adjacency storage under exact resource limits. -/
def compileWith (config : IndexConfig) (graph : Dependency.Graph String)
    (attributes : Array NodeAttributes) : Except IndexError Index := do
  if attributes.size != graph.nodeCount then
    throw <| .attributeCount graph.nodeCount attributes.size
  if config.maxNodes < graph.nodeCount then
    throw <| .nodeBudget graph.nodeCount config.maxNodes
  if config.maxEdges < graph.edgeCount then
    throw <| .edgeBudget graph.edgeCount config.maxEdges
  let coordinateMaximum := requiredCoordinate graph
  if config.maxCoordinate < coordinateMaximum then
    throw <| .coordinateBudget coordinateMaximum config.maxCoordinate
  let lexicalBytes := requiredLexicalBytes graph attributes
  if config.maxLexicalBytes < lexicalBytes then
    throw <| .lexicalByteBudget lexicalBytes config.maxLexicalBytes
  let mut headDense := Array.replicate graph.edgeCount 0
  let mut dependentDense := Array.replicate graph.edgeCount 0
  let mut degrees := Array.replicate (graph.nodeCount + 1) 0
  for row in [0:graph.nodeCount] do
    let start := graph.offsets[row]!
    let stop := graph.offsets[row + 1]!
    for edge in [start:stop] do
      dependentDense := dependentDense.set! edge (row + 1)
      let head := graph.heads[edge]!
      let headIndex ←
        match (denseLookup graph head).dense with
        | some value => pure value
        | none => throw <| .missingHead edge head
      headDense := headDense.set! edge headIndex
      degrees := degrees.set! headIndex (degrees[headIndex]! + 1)
  let mut outgoingOffsets := Array.emptyWithCapacity (graph.nodeCount + 2)
  let mut next := 0
  outgoingOffsets := outgoingOffsets.push 0
  for degree in degrees do
    next := next + degree
    outgoingOffsets := outgoingOffsets.push next
  let mut cursors := outgoingOffsets.extract 0 degrees.size
  let mut outgoingEdges := Array.replicate graph.edgeCount 0
  for edge in [0:graph.edgeCount] do
    let source := headDense[edge]!
    let cursor := cursors[source]!
    outgoingEdges := outgoingEdges.set! cursor edge
    cursors := cursors.set! source (cursor + 1)
  sealIndex graph attributes lexicalBytes coordinateMaximum headDense dependentDense
    outgoingOffsets outgoingEdges

/-- Compile a checked graph under production index limits. -/
@[inline] def compile (graph : Dependency.Graph String)
    (attributes : Array NodeAttributes) : Except IndexError Index :=
  compileWith {} graph attributes

/-- Compile a graph whose non-root nodes have no lexical attributes. -/
def compileGraphWith (config : IndexConfig) (graph : Dependency.Graph String) :
    Except IndexError Index := do
  if config.maxNodes < graph.nodeCount then
    throw <| .nodeBudget graph.nodeCount config.maxNodes
  if config.maxEdges < graph.edgeCount then
    throw <| .edgeBudget graph.edgeCount config.maxEdges
  let coordinateMaximum := requiredCoordinate graph
  if config.maxCoordinate < coordinateMaximum then
    throw <| .coordinateBudget coordinateMaximum config.maxCoordinate
  let relationBytes := graph.relations.foldl
    (fun total relation ↦ total + relation.utf8ByteSize) 0
  if config.maxLexicalBytes < relationBytes then
    throw <| .lexicalByteBudget relationBytes config.maxLexicalBytes
  compileWith config graph (Array.replicate graph.nodeCount {})

/-- Compile an attribute-free graph under production index limits. -/
@[inline] def compileGraph (graph : Dependency.Graph String) : Except IndexError Index :=
  compileGraphWith {} graph

end Index

/-- A statically selected optional node-attribute column. -/
inductive Field where
  | form
  | pos
  | lemma
  | ner
  deriving Repr, DecidableEq, Inhabited

/-- Boolean predicates over graph nodes and exact optional token attributes. -/
inductive NodePredicate where
  | any
  | root
  | node (id : NodeId)
  | attribute (field : Field) (value : String)
  | both (left right : NodePredicate)
  | either (left right : NodePredicate)
  | negate (body : NodePredicate)
  deriving Repr, DecidableEq, Inhabited

namespace NodePredicate

/-- Read one statically selected optional attribute. -/
@[inline] private def fieldValue (attributes : NodeAttributes) : Field → Option String
  | .form => attributes.form
  | .pos => attributes.pos
  | .lemma => attributes.lemma
  | .ner => attributes.ner

/-- Unchecked recursive semantics used only behind bounded public query boundaries. -/
private def acceptsUnchecked (index : Index) (dense : Nat) : NodePredicate → Bool
  | .any => index.nodeAt? dense |>.isSome
  | .root => dense = 0
  | .node expected => index.nodeAt? dense == some expected
  | .attribute field expected =>
      (index.attributesAt? dense).bind (fieldValue · field) == some expected
  | .both left right =>
      acceptsUnchecked index dense left && acceptsUnchecked index dense right
  | .either left right =>
      acceptsUnchecked index dense left || acceptsUnchecked index dense right
  | .negate body => !acceptsUnchecked index dense body

/-- Propositional denotation, explicitly closed over valid root-inclusive dense nodes. -/
def Denotes (index : Index) (dense : Nat) (predicate : NodePredicate) : Prop :=
  (index.nodeAt? dense).isSome = true ∧ acceptsUnchecked index dense predicate = true

/-- No predicate, including negation, denotes a dense ordinal absent from the index. -/
theorem not_denotes_of_invalid {index : Index} {dense : Nat} {predicate : NodePredicate}
    (invalid : index.nodeAt? dense = none) : ¬Denotes index dense predicate := by
  simp [Denotes, invalid]

end NodePredicate

/-- Direction of one direct dependency-edge test from the current query node. -/
inductive Direction where
  | incoming
  | outgoing
  deriving Repr, DecidableEq, Inhabited

/-- Typed direct dependency-graph query algebra. -/
inductive Query where
  | node (predicate : NodePredicate)
  | bind (name : String) (body : Query)
  | same (name : String)
  | both (left right : Query)
  | either (left right : Query)
  | negate (body : Query)
  | edge (direction : Direction) (relation : TextTest) (target : Query)
  deriving Repr, DecidableEq, Inhabited

namespace Query

/-- Test one direct incoming edge and continue at its head. -/
@[inline] def incoming (relation : TextTest) (target : Query) : Query :=
  .edge .incoming relation target

/-- Test one direct outgoing edge and continue at its dependent. -/
@[inline] def outgoing (relation : TextTest) (target : Query) : Query :=
  .edge .outgoing relation target

end Query

/-- One named node retained by a successful query. -/
structure Binding where
  name : String
  node : NodeId
  deriving Repr, DecidableEq, Inhabited

namespace Binding

@[inline] private def lookup? (bindings : Array Binding) (name : String) : Option NodeId :=
  (bindings.find? fun binding ↦ binding.name == name).map fun binding ↦ binding.node

/-- Bind a new name or enforce equality with its existing node. -/
private def insert? (bindings : Array Binding) (name : String) (node : NodeId) :
    Option (Array Binding) :=
  match lookup? bindings name with
  | none => some (bindings.push ⟨name, node⟩)
  | some existing => if existing == node then some bindings else none

end Binding

/-- Runtime limits for one bounded graph query. -/
structure SearchConfig where
  /-- Maximum evaluated syntax, edges, binding probes, and match-sealing checks. -/
  maxWork : Nat := 16_777_216
  /-- Maximum deterministic UTF-8 bytes charged to dynamic string comparisons. -/
  maxComparisonBytes : Nat := 268_435_456
  /-- Maximum intermediate environments retained across the complete evaluation. -/
  maxStates : Nat := 1_048_576
  /-- Maximum successful derivations retained in the final result. -/
  maxMatches : Nat := 1_048_576
  /-- Maximum constructors and `oneOf` choices in the complete pattern syntax tree. -/
  maxQueryNodes : Nat := 4_096
  /-- Requested nesting depth, clamped by the evaluator's hard stack-safety limit. -/
  maxQueryDepth : Nat := 256
  /-- Maximum UTF-8 bytes across every retained string occurrence in the query syntax. -/
  maxQueryLexicalBytes : Nat := 1_048_576
  /--
  Maximum coordinate in a query node literal; the default fixes coordinates to 32 bits.
  Raising it explicitly widens the arbitrary-precision comparison-cost envelope.
  -/
  maxQueryCoordinate : Nat := 4_294_967_295
  deriving Repr, DecidableEq, Inhabited

/-- Why a bounded graph query could not complete. -/
inductive SearchError where
  | workBudget (required limit : Nat)
  | comparisonByteBudget (required limit : Nat)
  | stateBudget (required limit : Nat)
  | matchBudget (required limit : Nat)
  | queryNodeBudget (required limit : Nat)
  | queryDepthBudget (required limit : Nat)
  | queryLexicalByteBudget (required limit : Nat)
  | queryCoordinateBudget (required limit : Nat)
  | emptyBindingName
  | inconsistentIndex
  deriving Repr, DecidableEq, Inhabited

/-- Exact bounded-query syntax requirements computed by the iterative preflight. -/
structure QueryRequirements where
  /-- Query, predicate, relation-test, and `oneOf` choice occurrences. -/
  nodes : Nat
  /-- Maximum combined query, predicate, and relation-test nesting depth. -/
  depth : Nat
  /-- UTF-8 bytes, counting every stored syntax-string occurrence exactly once. -/
  lexicalBytes : Nat
  /-- Largest natural coordinate in any query node literal. -/
  coordinateMaximum : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Check binding presence and uniqueness by deterministic first-binding-order comparisons. -/
private def checkBindings (index : Index) (bindings : Array Binding) : Bool := Id.run do
  for right in [0:bindings.size] do
    let binding := bindings[right]!
    unless (index.denseOf? binding.node).isSome do return false
    for left in [0:right] do
      if bindings[left]!.name == binding.name then return false
  return true

/-- One constructor-protected successful graph match. -/
structure Match (index : Index) where
  private mk ::
  /-- Anchor node tested by the outer query scan. -/
  anchor : NodeId
  /-- Named nodes in deterministic first-binding order. -/
  bindings : Array Binding
  private checked :
    ((index.denseOf? anchor).isSome && checkBindings index bindings) = true

namespace Match

/-- Executable well-formedness of one retained graph match. -/
def WF {index : Index} (matched : Match index) : Prop :=
  ((index.denseOf? matched.anchor).isSome && checkBindings index matched.bindings) = true

/-- Every emitted graph match has a present anchor and unique, present named nodes. -/
theorem wellFormed {index : Index} (matched : Match index) : matched.WF := matched.checked

/-- Read a named node from a successful match. -/
@[inline] def binding? {index : Index} (matched : Match index) (name : String) : Option NodeId :=
  Binding.lookup? matched.bindings name

end Match

private structure EvalState where
  work : Nat := 0
  retained : Nat := 0
  comparisonBytes : Nat := 0

/-- Charge one exact unit before syntax, edge, binding-probe, or sealing work. -/
private def charge (config : SearchConfig) (state : EvalState) :
    Except SearchError EvalState :=
  let required := state.work + 1
  if config.maxWork < required then .error (.workBudget required config.maxWork)
  else .ok { state with work := required }

/-- Charge several exact logical operations before performing their bounded implementation. -/
private def chargeMany (config : SearchConfig) (state : EvalState) (count : Nat) :
    Except SearchError EvalState :=
  let required := state.work + count
  if config.maxWork < required then .error (.workBudget required config.maxWork)
  else .ok { state with work := required }

/-- Charge deterministic UTF-8 comparison bytes before performing that operation. -/
private def chargeComparisonBytes (config : SearchConfig) (state : EvalState)
    (bytes : Nat) : Except SearchError EvalState :=
  let required := state.comparisonBytes + bytes
  if config.maxComparisonBytes < required then
    .error (.comparisonByteBudget required config.maxComparisonBytes)
  else
    .ok { state with comparisonBytes := required }

/-- Charge both full operands before a deterministic string comparison. -/
@[inline] private def chargeStringComparison (config : SearchConfig) (state : EvalState)
    (left right : String) : Except SearchError EvalState :=
  chargeComparisonBytes config state (left.utf8ByteSize + right.utf8ByteSize)

/-- Charge before retaining one intermediate environment. -/
private def retain (config : SearchConfig) (state : EvalState) :
    Except SearchError EvalState :=
  let required := state.retained + 1
  if config.maxStates < required then .error (.stateBudget required config.maxStates)
  else .ok { state with retained := required }

/-- Reserve several retained environments before allocating their destination array. -/
private def retainMany (config : SearchConfig) (state : EvalState) (count : Nat) :
    Except SearchError EvalState :=
  let required := state.retained + count
  if config.maxStates < required then .error (.stateBudget required config.maxStates)
  else .ok { state with retained := required }

/-- Hard recursive-evaluator depth cap, independent of caller-supplied policy. -/
private def maxEvaluationDepth : Nat := 256

/-- One work item in the iterative whole-pattern shape validator. -/
private inductive ShapeItem where
  | query (query : Query) (depth : Nat)
  | predicate (predicate : NodePredicate) (depth : Nat)
  | text (test : TextTest) (depth : Nat)
  deriving Inhabited

/-- UTF-8 bytes retained directly by one non-vocabulary whole-pattern work item. -/
private def ShapeItem.directLexicalBytes : ShapeItem → Nat
  | .query (.bind name _) _ | .query (.same name) _ => name.utf8ByteSize
  | .predicate (.attribute _ value) _ => value.utf8ByteSize
  | .text (.equal value) _ | .text (.prefix value) _ | .text (.suffix value) _ =>
      value.utf8ByteSize
  | _ => 0

/-- Add one item's lexical bytes, stopping before scanning later over-budget vocabulary values. -/
private def addLexicalBytes (config : SearchConfig) (total : Nat)
    (item : ShapeItem) : Except SearchError Nat := do
  let mut bytes := total
  match item with
  | .text (.oneOf values) _ =>
      for value in values do
        let required := bytes + value.utf8ByteSize
        if config.maxQueryLexicalBytes < required then
          throw <| .queryLexicalByteBudget required config.maxQueryLexicalBytes
        bytes := required
  | _ =>
      let required := bytes + item.directLexicalBytes
      if config.maxQueryLexicalBytes < required then
        throw <| .queryLexicalByteBudget required config.maxQueryLexicalBytes
      bytes := required
  return bytes

/-- Iteratively reject hostile total shape, depth, text, and empty names before recursion. -/
private def checkQueryShape (config : SearchConfig) (query : Query) :
    Except SearchError QueryRequirements := do
  let depthLimit := min config.maxQueryDepth maxEvaluationDepth
  let mut pending : Array ShapeItem := #[.query query 1]
  let mut cursor := 0
  let mut count := 0
  let mut deepest := 0
  let mut lexicalBytes := 0
  let mut coordinateMaximum := 0
  for _ in [0:config.maxQueryNodes + 1] do
    if cursor < pending.size then
      let current := pending[cursor]!
      cursor := cursor + 1
      let itemCount :=
        match current with
        | .text (.oneOf values) _ => values.size + 1
        | _ => 1
      let required := count + itemCount
      if config.maxQueryNodes < required then
        throw <| .queryNodeBudget required config.maxQueryNodes
      count := required
      let depth :=
        match current with
        | .query _ depth | .predicate _ depth | .text _ depth => depth
      if depthLimit < depth then
        throw <| .queryDepthBudget depth depthLimit
      deepest := max deepest depth
      lexicalBytes ← addLexicalBytes config lexicalBytes current
      let coordinate :=
        match current with
        | .predicate (.node expected) _ => nodeCoordinate expected
        | _ => 0
      let requiredCoordinate := max coordinateMaximum coordinate
      if config.maxQueryCoordinate < requiredCoordinate then
        throw <| .queryCoordinateBudget requiredCoordinate config.maxQueryCoordinate
      coordinateMaximum := requiredCoordinate
      match current with
      | .query (.node predicate) depth =>
          pending := pending.push (.predicate predicate (depth + 1))
      | .query (.same name) _ =>
          if name.isEmpty then throw .emptyBindingName
      | .query (.bind name body) depth =>
          if name.isEmpty then throw .emptyBindingName
          pending := pending.push (.query body (depth + 1))
      | .query (.negate body) depth =>
          pending := pending.push (.query body (depth + 1))
      | .query (.both left right) depth | .query (.either left right) depth =>
          pending := pending.push (.query left (depth + 1))
          pending := pending.push (.query right (depth + 1))
      | .query (.edge _ relation target) depth =>
          pending := pending.push (.text relation (depth + 1))
          pending := pending.push (.query target (depth + 1))
      | .predicate (.both left right) depth | .predicate (.either left right) depth =>
          pending := pending.push (.predicate left (depth + 1))
          pending := pending.push (.predicate right (depth + 1))
      | .predicate (.negate body) depth =>
          pending := pending.push (.predicate body (depth + 1))
      | .predicate _ _ | .text _ _ => pure ()
    else
      return ⟨count, deepest, lexicalBytes, coordinateMaximum⟩
  return ⟨count, deepest, lexicalBytes, coordinateMaximum⟩

/-- Iterate original incoming edge ordinals for one root-inclusive dense dependent. -/
@[inline] private def incomingBounds? (index : Index) (dense : Nat) : Option (Nat × Nat) := do
  if dense = 0 then none else
    let start ← index.graph.offsets[dense - 1]?
    let stop ← index.graph.offsets[dense]?
    return (start, stop)

/-- Evaluate and charge every visited recursive node-predicate constructor. -/
private def acceptsPredicate (index : Index) (config : SearchConfig) (dense : Nat) :
    NodePredicate → EvalState → Except SearchError (EvalState × Bool)
  | .any, state => do
      let state ← charge config state
      return (state, (index.nodeAt? dense).isSome)
  | .root, state => do
      let state ← charge config state
      return (state, dense = 0)
  | .node expected, state => do
      let state ← charge config state
      return (state, index.nodeAt? dense == some expected)
  | .attribute field expected, state => do
      let state ← charge config state
      let found :=
        match index.attributesAt? dense with
        | none => none
        | some attributes =>
            match field with
            | .form => attributes.form
            | .pos => attributes.pos
            | .lemma => attributes.lemma
            | .ner => attributes.ner
      match found with
      | none => return (state, false)
      | some value =>
          let state ← chargeStringComparison config state value expected
          return (state, value == expected)
  | .both left right, state => do
      let state ← charge config state
      let (state, accepted) ← acceptsPredicate index config dense left state
      if accepted then acceptsPredicate index config dense right state
      else return (state, false)
  | .either left right, state => do
      let state ← charge config state
      let (state, accepted) ← acceptsPredicate index config dense left state
      if accepted then return (state, true)
      else acceptsPredicate index config dense right state
  | .negate body, state => do
      let state ← charge config state
      let (state, accepted) ← acceptsPredicate index config dense body state
      return (state, !accepted)

/-- Evaluate and charge a relation test, including each inspected `oneOf` choice. -/
private def acceptsText (config : SearchConfig) (test : TextTest) (found : String)
    (state : EvalState) : Except SearchError (EvalState × Bool) := do
  let state ← charge config state
  match test with
  | .any => return (state, true)
  | .equal expected =>
      let state ← chargeStringComparison config state found expected
      return (state, found == expected)
  | .prefix expected =>
      let state ← chargeStringComparison config state found expected
      return (state, found.startsWith expected)
  | .suffix expected =>
      let state ← chargeStringComparison config state found expected
      return (state, found.endsWith expected)
  | .oneOf expected =>
      let mut state := state
      for candidate in expected do
        state ← charge config state
        state ← chargeStringComparison config state candidate found
        if candidate == found then return (state, true)
      return (state, false)

/-- Charge each binding-name comparison in a deterministic first-binding lookup. -/
private def lookupBinding (config : SearchConfig) (bindings : Array Binding)
    (name : String) (state : EvalState) :
    Except SearchError (EvalState × Option NodeId) := do
  let mut state := state
  for binding in bindings do
    state ← charge config state
    state ← chargeStringComparison config state binding.name name
    if binding.name == name then return (state, some binding.node)
  return (state, none)

namespace Query

/-- Compute exact whole-pattern requirements under bounded iterative preflight policy. -/
def requirementsWith (config : SearchConfig) (query : Query) :
    Except SearchError QueryRequirements :=
  checkQueryShape config query

/-- Compute exact whole-pattern requirements under production preflight policy. -/
@[inline] def requirements (query : Query) : Except SearchError QueryRequirements :=
  requirementsWith {} query

end Query

/-- A constructor-protected query validated once under one exact search policy. -/
structure CheckedQuery (config : SearchConfig) where
  private mk ::
  /-- Original query whose syntax passed bounded preflight. -/
  query : Query
  /-- Cached exact structural requirements from that preflight. -/
  requirements : QueryRequirements
  private checked : query.requirementsWith config = .ok requirements

namespace CheckedQuery

/-- Executable structural invariant carried by every checked query. -/
def WF {config : SearchConfig} (checked : CheckedQuery config) : Prop :=
  checked.query.requirementsWith config = .ok checked.requirements

/-- Every checked query retains the exact successful preflight outcome. -/
theorem wellFormed {config : SearchConfig} (checked : CheckedQuery config) : checked.WF :=
  checked.checked

end CheckedQuery

namespace Query

/-- Validate a query once and retain its exact structural requirements. -/
def checkWith (config : SearchConfig) (query : Query) :
    Except SearchError (CheckedQuery config) :=
  match checked : query.requirementsWith config with
  | .ok requirements => .ok ⟨query, requirements, checked⟩
  | .error cause => .error cause

/-- Validate a query once under production search policy. -/
@[inline] def check (query : Query) : Except SearchError (CheckedQuery {}) :=
  query.checkWith {}

end Query

/-- A bounded-search result retaining exact counters and validated-query provenance. -/
structure Result (index : Index) (config : SearchConfig) where
  /-- Query and exact preflight requirements used by this evaluation. -/
  checkedQuery : CheckedQuery config
  /-- Successful derivations in canonical anchor and traversal order. -/
  items : Array (Match index)
  /-- Exact logical evaluator charge; query lexical bytes are bounded independently. -/
  work : Nat
  /-- Exact number of intermediate environments cumulatively retained by the evaluator. -/
  states : Nat
  /-- Exact deterministic UTF-8 charge for dynamic string comparisons. -/
  comparisonBytes : Nat
  private workBound : work ≤ config.maxWork
  private stateBound : states ≤ config.maxStates
  private comparisonByteBound : comparisonBytes ≤ config.maxComparisonBytes
  private matchBound : items.size ≤ config.maxMatches

namespace Result

/-- Original structurally validated query evaluated to produce this result. -/
@[inline] def query {index : Index} {config : SearchConfig}
    (result : Result index config) : Query :=
  result.checkedQuery.query

/-- A result's query provenance retains its exact successful preflight outcome. -/
theorem query_wellFormed {index : Index} {config : SearchConfig}
    (result : Result index config) : result.checkedQuery.WF :=
  result.checkedQuery.wellFormed

/-- Successful bounded search never exceeds its retained work policy. -/
theorem work_le {index : Index} {config : SearchConfig} (result : Result index config) :
    result.work ≤ config.maxWork := result.workBound

/-- Successful bounded search never exceeds its intermediate-state policy. -/
theorem states_le {index : Index} {config : SearchConfig} (result : Result index config) :
    result.states ≤ config.maxStates := result.stateBound

/-- Successful bounded search never exceeds its dynamic comparison-byte policy. -/
theorem comparisonBytes_le {index : Index} {config : SearchConfig}
    (result : Result index config) : result.comparisonBytes ≤ config.maxComparisonBytes :=
  result.comparisonByteBound

/-- Successful bounded search never exceeds its retained result policy. -/
theorem matches_size_le {index : Index} {config : SearchConfig}
    (result : Result index config) : result.items.size ≤ config.maxMatches :=
  result.matchBound

end Result

namespace NodePredicate

/-- Evaluate a predicate only after bounded shape/text preflight and a valid-node check. -/
def acceptsWith (index : Index) (config : SearchConfig) (dense : Nat)
    (predicate : NodePredicate) : Except SearchError Bool := do
  let _ ← checkQueryShape config (.node predicate)
  if (index.nodeAt? dense).isNone then return false
  let (_, accepted) ← acceptsPredicate index config dense predicate {}
  return accepted

/-- Evaluate a predicate under production shape, text, work, and stack-safety limits. -/
@[inline] def accepts (index : Index) (dense : Nat) (predicate : NodePredicate) :
    Except SearchError Bool :=
  acceptsWith index {} dense predicate

end NodePredicate

/-- A continuation that can stop derivation search after observing one accepted environment. -/
private abbrev AcceptContinuation :=
  Array Binding → EvalState → Except SearchError (EvalState × Bool)

/--
Search derivations in canonical order without allocating result arrays, stopping when the supplied
continuation accepts one. This is the existence kernel used by negation.
-/
private def searchUntil (index : Index) (config : SearchConfig) (dense : Nat) :
    Query → Array Binding → EvalState → AcceptContinuation →
      Except SearchError (EvalState × Bool)
  | .node predicate, bindings, state, accept => do
      let state ← charge config state
      let (state, accepted) ← acceptsPredicate index config dense predicate state
      if accepted then
        let state ← retain config state
        accept bindings state
      else
        return (state, false)
  | .same name, bindings, state, accept => do
      let state ← charge config state
      let node ←
        match index.nodeAt? dense with
        | some value => pure value
        | none => throw .inconsistentIndex
      let (state, existing) ← lookupBinding config bindings name state
      if existing == some node then
        let state ← retain config state
        accept bindings state
      else
        return (state, false)
  | .bind name body, bindings, state, accept => do
      let state ← charge config state
      let node ←
        match index.nodeAt? dense with
        | some value => pure value
        | none => throw .inconsistentIndex
      let (state, existing) ← lookupBinding config bindings name state
      match existing with
      | some prior =>
          if prior == node then searchUntil index config dense body bindings state accept
          else return (state, false)
      | none =>
          let state ← retain config state
          searchUntil index config dense body (bindings.push ⟨name, node⟩) state accept
  | .both left right, bindings, state, accept => do
      let state ← charge config state
      searchUntil index config dense left bindings state fun environment state ↦
        searchUntil index config dense right environment state accept
  | .either left right, bindings, state, accept => do
      let state ← charge config state
      let leftResult ← searchUntil index config dense left bindings state accept
      if leftResult.2 then return leftResult
      searchUntil index config dense right bindings leftResult.1 accept
  | .negate body, bindings, state, accept => do
      let state ← charge config state
      let found ← searchUntil index config dense body bindings state fun _ state ↦
        return (state, true)
      if found.2 then
        return (found.1, false)
      else
        let state ← retain config found.1
        accept bindings state
  | .edge .incoming relation target, bindings, state, accept => do
      let state ← charge config state
      let mut state := state
      match incomingBounds? index dense with
      | none => pure ()
      | some (start, stop) =>
          for edge in [start:stop] do
            state ← charge config state
            let tested ← acceptsText config relation index.graph.relations[edge]! state
            state := tested.1
            if tested.2 then
              let neighbor := index.headDense[edge]!
              let found ← searchUntil index config neighbor target bindings state accept
              state := found.1
              if found.2 then return found
      return (state, false)
  | .edge .outgoing relation target, bindings, state, accept => do
      let state ← charge config state
      let mut state := state
      let start := index.outgoingOffsets.getD dense 0
      let stop := index.outgoingOffsets.getD (dense + 1) start
      for cursor in [start:stop] do
        state ← charge config state
        let edge := index.outgoingEdges[cursor]!
        let tested ← acceptsText config relation index.graph.relations[edge]! state
        state := tested.1
        if tested.2 then
          let neighbor := index.dependentDense[edge]!
          let found ← searchUntil index config neighbor target bindings state accept
          state := found.1
          if found.2 then return found
      return (state, false)
  termination_by query => query

/-- Evaluate one query while threading exact work and named-node environments. -/
private def eval (index : Index) (config : SearchConfig) :
    Query → Nat → Array Binding → EvalState →
      Except SearchError (EvalState × Array (Array Binding))
  | .node predicate, dense, bindings, state => do
      let state ← charge config state
      let (state, accepted) ← acceptsPredicate index config dense predicate state
      if accepted then
        let state ← retain config state
        return (state, #[bindings])
      else
        return (state, #[])
  | .same name, dense, bindings, state => do
      let state ← charge config state
      let node ←
        match index.nodeAt? dense with
        | some value => pure value
        | none => throw .inconsistentIndex
      let (state, existing) ← lookupBinding config bindings name state
      if existing == some node then
        let state ← retain config state
        return (state, #[bindings])
      else
        return (state, #[])
  | .bind name body, dense, bindings, state => do
      let state ← charge config state
      let node ←
        match index.nodeAt? dense with
        | some value => pure value
        | none => throw .inconsistentIndex
      let (state, existing) ← lookupBinding config bindings name state
      match existing with
      | some prior =>
          if prior == node then eval index config body dense bindings state
          else return (state, #[])
      | none =>
          let state ← retain config state
          eval index config body dense (bindings.push ⟨name, node⟩) state
  | .both left right, dense, bindings, state => do
      let state ← charge config state
      let (state, leftResults) ← eval index config left dense bindings state
      let mut state := state
      let mut output := #[]
      for environment in leftResults do
        let found ← eval index config right dense environment state
        state := found.1
        for result in found.2 do
          state ← retain config state
          output := output.push result
      return (state, output)
  | .either left right, dense, bindings, state => do
      let state ← charge config state
      let (state, leftResults) ← eval index config left dense bindings state
      let (state, rightResults) ← eval index config right dense bindings state
      let resultCount := leftResults.size + rightResults.size
      let state ← retainMany config state resultCount
      let mut output := Array.emptyWithCapacity resultCount
      for result in leftResults do
        output := output.push result
      for result in rightResults do
        output := output.push result
      return (state, output)
  | .negate body, dense, bindings, state => do
      let state ← charge config state
      let found ← searchUntil index config dense body bindings state fun _ state ↦
        return (state, true)
      if found.2 then
        return (found.1, #[])
      else
        let state ← retain config found.1
        return (state, #[bindings])
  | .edge .incoming relation target, dense, bindings, state => do
      let state ← charge config state
      let mut state := state
      let mut output := #[]
      match incomingBounds? index dense with
      | none => pure ()
      | some (start, stop) =>
          for edge in [start:stop] do
            state ← charge config state
            let tested ← acceptsText config relation index.graph.relations[edge]! state
            state := tested.1
            if tested.2 then
              let neighbor := index.headDense[edge]!
              let found ← eval index config target neighbor bindings state
              state := found.1
              for result in found.2 do
                state ← retain config state
                output := output.push result
      return (state, output)
  | .edge .outgoing relation target, dense, bindings, state => do
      let state ← charge config state
      let mut state := state
      let mut output := #[]
      let start := index.outgoingOffsets.getD dense 0
      let stop := index.outgoingOffsets.getD (dense + 1) start
      for cursor in [start:stop] do
        state ← charge config state
        let edge := index.outgoingEdges[cursor]!
        let tested ← acceptsText config relation index.graph.relations[edge]! state
        state := tested.1
        if tested.2 then
          let neighbor := index.dependentDense[edge]!
          let found ← eval index config target neighbor bindings state
          state := found.1
          for result in found.2 do
            state ← retain config state
            output := output.push result
      return (state, output)

/-- Charge and seal one runtime environment behind the public match invariant. -/
private def sealMatch (index : Index) (config : SearchConfig) (state : EvalState)
    (anchor : NodeId) (bindings : Array Binding) :
    Except SearchError (EvalState × Match index) := do
  let mut state ← charge config state
  let anchorLookup := Index.denseLookup index.graph anchor
  let mut lookupComparisons := anchorLookup.comparisons
  let mut nameBytes := 0
  for binding in bindings do
    let bindingLookup := Index.denseLookup index.graph binding.node
    lookupComparisons := lookupComparisons + bindingLookup.comparisons
    nameBytes := nameBytes + binding.name.utf8ByteSize
  let pairComparisons := bindings.size * (bindings.size - 1) / 2
  -- Charge the observed lookup pass and its certificate replay, plus every name pair.
  state ← chargeMany config state (2 * lookupComparisons + pairComparisons)
  state ← chargeComparisonBytes config state ((bindings.size - 1) * nameBytes)
  match checked : (index.denseOf? anchor).isSome && checkBindings index bindings with
  | true => return (state, ⟨anchor, bindings, checked⟩)
  | false => throw .inconsistentIndex

/-- Constructor-protected resumable search retaining exact global budgets and canonical order. -/
structure SearchCursor (index : Index) (config : SearchConfig) where
  private mk ::
  private checkedQuery : CheckedQuery config
  private nextDense : Nat
  private items : Array (Match index)
  private work : Nat
  private states : Nat
  private comparisonBytes : Nat

namespace SearchCursor

/-- Initialize a resumable search from a query whose bounded preflight already succeeded. -/
@[inline] def startChecked {config : SearchConfig} (index : Index)
    (checked : CheckedQuery config) : SearchCursor index config :=
  ⟨checked, 0, #[], 0, 0, 0⟩

/-- Validate a query once and initialize a resumable bounded search. -/
def startWith (index : Index) (config : SearchConfig) (query : Query) :
    Except SearchError (SearchCursor index config) := do
  let checked ← query.checkWith config
  return startChecked index checked

/-- Original structurally validated query advanced by this cursor. -/
@[inline] def query {index : Index} {config : SearchConfig}
    (cursor : SearchCursor index config) : Query :=
  cursor.checkedQuery.query

/-- A cursor's query provenance retains its exact successful preflight outcome. -/
theorem query_wellFormed {index : Index} {config : SearchConfig}
    (cursor : SearchCursor index config) : cursor.checkedQuery.WF :=
  cursor.checkedQuery.wellFormed

/-- Whether every root-inclusive anchor has been evaluated. -/
@[inline] def finished {index : Index} {config : SearchConfig}
    (cursor : SearchCursor index config) : Bool :=
  index.nodeCount ≤ cursor.nextDense

/-- Evaluate at most one canonical anchor while preserving every global counter. -/
def advance {index : Index} {config : SearchConfig}
    (cursor : SearchCursor index config) : Except SearchError (SearchCursor index config) := do
  if index.nodeCount ≤ cursor.nextDense then return cursor
  let dense := cursor.nextDense
  let initial : EvalState :=
    ⟨cursor.work, cursor.states, cursor.comparisonBytes⟩
  let found ← eval index config cursor.checkedQuery.query dense #[] initial
  let mut state := found.1
  let mut items := cursor.items
  let anchor ←
    match index.nodeAt? dense with
    | some value => pure value
    | none => throw .inconsistentIndex
  for bindings in found.2 do
    let required := items.size + 1
    if config.maxMatches < required then
      throw <| .matchBudget required config.maxMatches
    let sealed ← sealMatch index config state anchor bindings
    state := sealed.1
    items := items.push sealed.2
  return ⟨cursor.checkedQuery, dense + 1, items, state.work, state.retained,
    state.comparisonBytes⟩

/-- Evaluate up to `count` canonical anchors, stopping early after completion. -/
def advanceBy {index : Index} {config : SearchConfig}
    (count : Nat) (cursor : SearchCursor index config) :
    Except SearchError (SearchCursor index config) := do
  let mut current := cursor
  for _ in [0:count] do
    if current.finished then return current
    current ← current.advance
  return current

/-- Seal a completed cursor as a certified result; incomplete cursors return `none`. -/
def result? {index : Index} {config : SearchConfig}
    (cursor : SearchCursor index config) : Option (Result index config) :=
  if index.nodeCount ≤ cursor.nextDense then
    if workBound : cursor.work ≤ config.maxWork then
      if stateBound : cursor.states ≤ config.maxStates then
        if comparisonBound : cursor.comparisonBytes ≤ config.maxComparisonBytes then
          if matchBound : cursor.items.size ≤ config.maxMatches then
            some ⟨cursor.checkedQuery, cursor.items, cursor.work, cursor.states,
              cursor.comparisonBytes, workBound, stateBound, comparisonBound, matchBound⟩
          else none
        else none
      else none
    else none
  else none

end SearchCursor

/-- Find every derivation from a query whose bounded preflight already succeeded. -/
def findAllCheckedWith (index : Index) {config : SearchConfig}
    (checked : CheckedQuery config) : Except SearchError (Result index config) := do
  let mut cursor := SearchCursor.startChecked index checked
  cursor ← cursor.advanceBy index.nodeCount
  match cursor.result? with
  | some result => return result
  | none => throw .inconsistentIndex

/-- Find every successful derivation under exact work and output limits. -/
def findAllWith (index : Index) (config : SearchConfig) (query : Query) :
    Except SearchError (Result index config) := do
  let checked ← query.checkWith config
  findAllCheckedWith index checked

/-- Find every successful derivation under production query limits. -/
@[inline] def findAll (index : Index) (query : Query) :
    Except SearchError (Result index {}) :=
  findAllWith index {} query

/-- Plain coordinates emitted by the intentionally slow executable denotation. -/
structure ReferenceMatch where
  anchor : NodeId
  bindings : Array Binding
  deriving Repr, DecidableEq, Inhabited

/-- Evaluate one query by scanning reconstructed rows instead of the outgoing index. -/
private def referenceEval (index : Index) (rows : Array (Dependency.Row String)) :
    Query → NodeId → Array Binding → Array (Array Binding)
  | .node predicate, node, bindings =>
      match index.denseOf? node with
      | some dense =>
          if NodePredicate.acceptsUnchecked index dense predicate then #[bindings] else #[]
      | none => #[]
  | .same name, node, bindings =>
      if Binding.lookup? bindings name == some node then #[bindings] else #[]
  | .bind name body, node, bindings =>
      match Binding.insert? bindings name node with
      | some next => referenceEval index rows body node next
      | none => #[]
  | .both left right, node, bindings => Id.run do
      let mut output := #[]
      for environment in referenceEval index rows left node bindings do
        for result in referenceEval index rows right node environment do
          output := output.push result
      return output
  | .either left right, node, bindings => Id.run do
      let leftResults := referenceEval index rows left node bindings
      let rightResults := referenceEval index rows right node bindings
      let mut output := Array.emptyWithCapacity (leftResults.size + rightResults.size)
      for result in leftResults do output := output.push result
      for result in rightResults do output := output.push result
      return output
  | .negate body, node, bindings =>
      if (referenceEval index rows body node bindings).isEmpty then #[bindings] else #[]
  | .edge .incoming relation target, node, bindings => Id.run do
      let mut output := #[]
      for row in rows do
        if row.dependent == node then
          for arc in row.incoming do
            if relation.accepts arc.relation then
              for result in referenceEval index rows target arc.head bindings do
                output := output.push result
      return output
  | .edge .outgoing relation target, node, bindings => Id.run do
      let mut output := #[]
      for row in rows do
        for arc in row.incoming do
          if arc.head == node && relation.accepts arc.relation then
            for result in referenceEval index rows target row.dependent bindings do
              output := output.push result
      return output
  termination_by query => query

/--
Enumerate the unbounded executable denotation by scanning every canonical incoming row.

This deliberately slow oracle is for proofs, differential tests, and small trusted inputs. Public
application boundaries should use `findAllWith`, whose dual index and exact budgets are bounded.
-/
def referenceFindAll (index : Index) (query : Query) : Array ReferenceMatch := Id.run do
  let rows := index.graph.toRows
  let mut output := #[]
  for dense in [0:index.nodeCount] do
    match index.nodeAt? dense with
    | none => pure ()
    | some anchor =>
        for bindings in referenceEval index rows query anchor #[] do
          output := output.push ⟨anchor, bindings⟩
  return output

namespace Query

/-- Propositional graph-query denotation at one anchor with exact named-node bindings. -/
def Denotes (index : Index) (query : Query) (anchor : NodeId)
    (bindings : Array Binding) : Prop :=
  ReferenceMatch.mk anchor bindings ∈ referenceFindAll index query

instance (index : Index) (query : Query) (anchor : NodeId) (bindings : Array Binding) :
    Decidable (Denotes index query anchor bindings) := by
  unfold Denotes
  infer_instance

end Query

namespace Result

/-- Erase match certificates to the same coordinates returned by the reference evaluator. -/
def referenceView {index : Index} {config : SearchConfig}
    (result : Result index config) : Array ReferenceMatch :=
  result.items.map fun matched ↦ ⟨matched.anchor, matched.bindings⟩

end Result

end Nlp.Pattern.GraphQuery
