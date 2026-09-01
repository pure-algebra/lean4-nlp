import Std.Data.HashMap
import Nlp.Core.Data.Dependency

/-!
# Checked enhanced-dependency graphs

Enhanced dependencies are directed multigraphs rather than trees: a dependent may have several
heads, relative constructions may introduce cycles, and coordination may introduce several root
arcs. This module stores incoming arcs in canonical compressed-sparse-row form and validates the
entire graph before exposing its private constructor.
-/

namespace Nlp.Dependency

/-- A stable dependency-graph node identifier, including future empty and copied nodes. -/
inductive NodeId where
  /-- The artificial sentence root. It may head arcs but never appears as a stored node. -/
  | root
  /-- An ordinary positive, one-based sentence word. -/
  | word (index : Nat)
  /-- The positive `copy`-th empty node immediately after `anchor`; anchor zero is allowed. -/
  | empty (anchor copy : Nat)
  /-- The positive `copy`-th graph-only copy of a positive ordinary word. -/
  | copy (index copy : Nat)
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

namespace NodeId

/-- Compare natural-number coordinates without relying on an ambient node order. -/
@[inline] private def compareNat (left right : Nat) : Ordering :=
  if left < right then .lt else if left = right then .eq else .gt

/-- The canonical major coordinate, shared by words and nodes anchored at a word. -/
@[inline] def major : NodeId → Nat
  | .root => 0
  | .word index => index
  | .empty anchor _ => anchor
  | .copy index _ => index

/-- Canonical kind rank at one major coordinate: word, copy, then empty node. -/
@[inline] def kindRank : NodeId → Nat
  | .root | .word _ => 0
  | .copy _ _ => 1
  | .empty _ _ => 2

/-- Canonical minor coordinate within graph-only copies or empty nodes. -/
@[inline] def minor : NodeId → Nat
  | .root | .word _ => 0
  | .empty _ minorIndex | .copy _ minorIndex => minorIndex

/-- Compare nodes in root/CoNLL-U position order, with graph copies before empty nodes. -/
def compare (left right : NodeId) : Ordering :=
  match compareNat left.major right.major with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
    match compareNat left.kindRank right.kindRank with
    | .lt => .lt
    | .gt => .gt
    | .eq => compareNat left.minor right.minor

/-- Whether the first node strictly precedes the second in canonical graph order. -/
@[inline] def precedes (left right : NodeId) : Bool := left.compare right == .lt

/-- Whether a non-root node uses the required positive coordinates. -/
@[inline] def valid : NodeId → Bool
  | .root => true
  | .word index => 0 < index
  | .empty _ minorIndex => 0 < minorIndex
  | .copy index minorIndex => 0 < index && 0 < minorIndex

/-- Node identifiers use the graph's canonical position order. -/
instance : Ord NodeId where
  compare := NodeId.compare

end NodeId

/-- Provenance class retained for every enhanced-graph arc. -/
inductive Origin where
  /-- The arc descends from the checked basic dependency tree. -/
  | basic
  /-- The arc was introduced by an enhancement rule. -/
  | enhanced
  /-- The arc was introduced with an elided-predicate empty node. -/
  | empty
  /-- The arc was introduced with an enhanced++ copied node. -/
  | copy
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- One labeled incoming arc before or after CSR compilation. -/
structure Arc (R : Type) where
  /-- The artificial root or a stored graph node that governs the dependent. -/
  head : NodeId
  /-- Caller-defined dependency relation. -/
  relation : R
  /-- How this arc entered the enhanced graph. -/
  origin : Origin
  deriving Repr, DecidableEq

/-- One dependent and its nonempty, canonically ordered incoming arc row. -/
structure Row (R : Type) where
  /-- A valid non-root graph node. -/
  dependent : NodeId
  /-- Incoming arcs ordered by head and then relation. -/
  incoming : Array (Arc R)
  deriving Repr, DecidableEq

/-- Resource policy for compiling a checked graph. -/
structure GraphConfig where
  /-- Maximum aggregate entries retained by the five CSR columns. -/
  maxEntries : Nat := 33_554_432
  deriving Repr, DecidableEq, Inhabited

namespace GraphConfig

/-- Production graph-compilation resource limits. -/
def default : GraphConfig := {}

end GraphConfig

/-- A deterministic failure from CSR validation or graph compilation. -/
inductive GraphError (R : Type) where
  /-- The five retained CSR columns exceed the configured aggregate budget. -/
  | entryBudget (required limit : Nat)
  /-- The parallel edge columns do not have one entry per head. -/
  | columnCount (heads relations origins : Nat)
  /-- CSR offsets do not contain one boundary before and after every node row. -/
  | offsetCount (expected found : Nat)
  /-- A CSR row boundary is noncanonical, empty, or outside the edge columns. -/
  | invalidOffset (row start stop edges : Nat)
  /-- The artificial root appeared as a stored dependent node. -/
  | rootNode (row : Nat)
  /-- A word, empty node, or copied node has an invalid positive coordinate. -/
  | invalidNode (node : NodeId)
  /-- Stored dependent nodes are not in strict canonical order. -/
  | nodeOrder (left right : NodeId)
  /-- An arc names a valid node that is absent from the stored dependent set. -/
  | missingHead (dependent head : NodeId)
  /-- A dependency node governs itself. -/
  | selfEdge (dependent : NodeId)
  /-- A row repeats an exact head-and-relation pair, regardless of provenance. -/
  | duplicateArc (dependent head : NodeId) (relation : R)
  /-- Incoming arcs are not ordered by head and then relation. -/
  | incomingOrder (dependent leftHead : NodeId) (leftRelation : R)
      (rightHead : NodeId) (rightRelation : R)
  /-- No stored node is governed by the artificial root. -/
  | noRoot
  /-- A stored node is not reachable by directed arcs from the artificial root. -/
  | unreachable (node : NodeId)
  deriving Repr

namespace Graph

/-- Aggregate retained entries for nodes, offsets, and three parallel edge columns. -/
@[inline] def requiredEntries (nodes edges : Nat) : Nat :=
  nodes + (nodes + 1) + 3 * edges

/-- Compare two incoming arc keys without considering their provenance. -/
@[inline] private def compareArcKey {R : Type} [Ord R]
    (leftHead : NodeId) (leftRelation : R)
    (rightHead : NodeId) (rightRelation : R) : Ordering :=
  match leftHead.compare rightHead with
  | .lt => .lt
  | .gt => .gt
  | .eq => compare leftRelation rightRelation

/-- Build the node-to-dense-index map after node validation has succeeded. -/
private def nodeIndex (nodes : Array NodeId) : Std.HashMap NodeId Nat := Id.run do
  let mut result : Std.HashMap NodeId Nat := Std.HashMap.emptyWithCapacity nodes.size
  for index in [0:nodes.size] do
    result := result.insert nodes[index]! index
  return result

/-- Validate stored nodes and return their dense lookup table. -/
private def checkNodes {R : Type} (nodes : Array NodeId) : Except (GraphError R)
    (Std.HashMap NodeId Nat) := do
  for index in [0:nodes.size] do
    let node := nodes[index]!
    if node == .root then
      throw <| .rootNode index
    unless node.valid do
      throw <| .invalidNode node
    if 0 < index then
      let previous := nodes[index - 1]!
      unless previous.precedes node do
        throw <| .nodeOrder previous node
  return nodeIndex nodes

/-- Mark every dense node reachable from root through flat outgoing CSR storage. -/
private def reachable (offsets targets : Array Nat) : Array Bool := Id.run do
  let bucketCount := offsets.size - 1
  let mut seen := Array.replicate bucketCount false
  let mut queue := Array.emptyWithCapacity bucketCount
  if 0 < bucketCount then
    seen := seen.set! 0 true
    queue := queue.push 0
  let mut cursor := 0
  for _ in [0:bucketCount] do
    if cursor < queue.size then
      let current := queue[cursor]!
      cursor := cursor + 1
      let start := offsets[current]!
      let stop := offsets[current + 1]!
      for edgeIndex in [start:stop] do
        let next := targets[edgeIndex]!
        unless seen[next]! do
          seen := seen.set! next true
          queue := queue.push next
  return seen

/--
Validate raw compressed-sparse-row graph storage.

Offsets have length `nodes.size + 1`, begin at zero, and bound a nonempty row for every node.
Every non-root head resolves through the node array. Incoming rows are strictly ordered by head
and relation, so exact duplicates are adjacent and rejected in one scan.
-/
def checkCSR {R : Type} [Ord R] (nodes : Array NodeId) (offsets : Array Nat)
    (heads : Array NodeId) (relations : Array R) (origins : Array Origin) :
    Except (GraphError R) Unit := do
  unless heads.size = relations.size && heads.size = origins.size do
    throw <| .columnCount heads.size relations.size origins.size
  let expectedOffsets := nodes.size + 1
  unless offsets.size = expectedOffsets do
    throw <| .offsetCount expectedOffsets offsets.size
  unless offsets[0]? = some 0 do
    throw <| .invalidOffset 0 (offsets[0]?.getD 0) (offsets[1]?.getD 0) heads.size
  let indices ← checkNodes nodes
  let mut foundRoot := false
  let mut outDegrees := Array.replicate (nodes.size + 1) 0
  let mut denseHeads := Array.replicate heads.size 0
  for rowIndex in [0:nodes.size] do
    let start := offsets[rowIndex]!
    let stop := offsets[rowIndex + 1]!
    unless start < stop && stop ≤ heads.size do
      throw <| .invalidOffset rowIndex start stop heads.size
    let dependent := nodes[rowIndex]!
    for edgeIndex in [start:stop] do
      let head := heads[edgeIndex]!
      let relation : R ←
        match relations[edgeIndex]? with
        | some relation => pure relation
        | none => throw <| .columnCount heads.size relations.size origins.size
      unless head.valid do
        throw <| .invalidNode head
      let denseHead ←
        if head == .root then
          foundRoot := true
          pure 0
        else
          match indices.get? head with
          | some index => pure (index + 1)
          | none => throw <| .missingHead dependent head
      if head == dependent then
        throw <| .selfEdge dependent
      if start < edgeIndex then
        let leftIndex := edgeIndex - 1
        let leftHead := heads[leftIndex]!
        let leftRelation : R ←
          match relations[leftIndex]? with
          | some relation => pure relation
          | none => throw <| .columnCount heads.size relations.size origins.size
        match compareArcKey leftHead leftRelation head relation with
        | .lt => pure ()
        | .eq => throw <| .duplicateArc dependent head relation
        | .gt =>
          throw <| GraphError.incomingOrder dependent leftHead leftRelation head relation
      denseHeads := denseHeads.set! edgeIndex denseHead
      outDegrees := outDegrees.set! denseHead (outDegrees[denseHead]! + 1)
  let finalOffset := offsets.back?.getD 0
  unless finalOffset = heads.size do
    throw <| .invalidOffset nodes.size finalOffset finalOffset heads.size
  unless nodes.isEmpty || foundRoot do
    throw .noRoot
  let mut outgoingOffsets := Array.emptyWithCapacity (outDegrees.size + 1)
  let mut nextOffset := 0
  outgoingOffsets := outgoingOffsets.push 0
  for degree in outDegrees do
    nextOffset := nextOffset + degree
    outgoingOffsets := outgoingOffsets.push nextOffset
  let mut cursors := Array.emptyWithCapacity outDegrees.size
  for index in [0:outDegrees.size] do
    cursors := cursors.push outgoingOffsets[index]!
  let mut outgoingTargets := Array.replicate heads.size 0
  for rowIndex in [0:nodes.size] do
    let start := offsets[rowIndex]!
    let stop := offsets[rowIndex + 1]!
    for edgeIndex in [start:stop] do
      let denseHead := denseHeads[edgeIndex]!
      let targetIndex := cursors[denseHead]!
      outgoingTargets := outgoingTargets.set! targetIndex (rowIndex + 1)
      cursors := cursors.set! denseHead (targetIndex + 1)
  let seen := reachable outgoingOffsets outgoingTargets
  for index in [0:nodes.size] do
    unless seen[index + 1]! do
      throw <| .unreachable nodes[index]!

end Graph

/--
A proof-carrying enhanced-dependency graph in incoming compressed-sparse-row form.

The artificial root is implicit and absent from `nodes`. Row `i` occupies
`offsets[i] .. offsets[i + 1]` in the parallel head, relation, and origin columns.
-/
structure Graph (R : Type) [Ord R] where
  private mk ::
  /-- Strictly ordered non-root dependent nodes. -/
  nodes : Array NodeId
  /-- One CSR boundary before and after every dependent row. -/
  offsets : Array Nat
  /-- Canonically ordered incoming heads. -/
  heads : Array NodeId
  /-- Relations aligned with incoming heads. -/
  relations : Array R
  /-- Provenance aligned with incoming heads. -/
  origins : Array Origin
  private checked : Graph.checkCSR nodes offsets heads relations origins = .ok ()

namespace Graph

/-- Executable semantic well-formedness of a stored enhanced-dependency graph. -/
def WF [Ord R] (graph : Graph R) : Prop :=
  checkCSR graph.nodes graph.offsets graph.heads graph.relations graph.origins = .ok ()

/-- Every constructible graph passes the complete executable CSR checker. -/
theorem wellFormed [Ord R] (graph : Graph R) : graph.WF := graph.checked

/-- Number of stored non-root graph nodes. -/
@[inline] def nodeCount [Ord R] (graph : Graph R) : Nat := graph.nodes.size

/-- Number of stored directed labeled arcs. -/
@[inline] def edgeCount [Ord R] (graph : Graph R) : Nat := graph.heads.size

/-- Check raw storage and seal it behind the private graph constructor. -/
private def ofCSR [Ord R] (nodes : Array NodeId) (offsets : Array Nat)
    (heads : Array NodeId) (relations : Array R) (origins : Array Origin) :
    Except (GraphError R) (Graph R) :=
  match checked : checkCSR nodes offsets heads relations origins with
  | .ok () => .ok ⟨nodes, offsets, heads, relations, origins, checked⟩
  | .error cause => .error cause

/-- Compile canonical incoming rows under an explicit aggregate-entry budget. -/
def ofRowsWith [Ord R] (config : GraphConfig) (rows : Array (Row R)) :
    Except (GraphError R) (Graph R) := do
  let edges := rows.foldl (init := 0) fun total row ↦ total + row.incoming.size
  let required := requiredEntries rows.size edges
  if config.maxEntries < required then
    throw <| .entryBudget required config.maxEntries
  let mut nodes := Array.emptyWithCapacity rows.size
  let mut offsets := Array.emptyWithCapacity (rows.size + 1)
  let mut heads := Array.emptyWithCapacity edges
  let mut relations := Array.emptyWithCapacity edges
  let mut origins := Array.emptyWithCapacity edges
  offsets := offsets.push 0
  for row in rows do
    nodes := nodes.push row.dependent
    for arc in row.incoming do
      heads := heads.push arc.head
      relations := relations.push arc.relation
      origins := origins.push arc.origin
    offsets := offsets.push heads.size
  ofCSR nodes offsets heads relations origins

/-- Compile canonical incoming rows under production resource limits. -/
@[inline] def ofRows [Ord R] (rows : Array (Row R)) :
    Except (GraphError R) (Graph R) :=
  ofRowsWith .default rows

/-- Compile a checked basic tree as a graph under an explicit aggregate-entry budget. -/
def ofTreeWith [Ord R] (config : GraphConfig) (tree : Tree R) :
    Except (GraphError R) (Graph R) := do
  let mut rows := Array.emptyWithCapacity tree.heads.size
  for index in [0:tree.heads.size] do
    let headIndex := tree.heads[index]!
    let head := if headIndex = 0 then .root else .word headIndex
    let relation ←
      match tree.relations[index]? with
      | some relation => pure relation
      | none => throw <| .columnCount tree.heads.size tree.relations.size 0
    let arc : Arc R := ⟨head, relation, .basic⟩
    rows := rows.push ⟨.word (index + 1), #[arc]⟩
  ofRowsWith config rows

/-- Compile a checked basic tree as a production enhanced-graph seed. -/
@[inline] def ofTree [Ord R] (tree : Tree R) : Except (GraphError R) (Graph R) :=
  ofTreeWith .default tree

/-- Binary search for one node's dense row index in the canonical node array. -/
private def findNodeAux (nodes : Array NodeId) (target : NodeId) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, lower, upper =>
    if lower < upper then
      let middle := lower + (upper - lower) / 2
      match nodes[middle]? with
      | none => none
      | some node =>
        match target.compare node with
        | .eq => some middle
        | .lt => findNodeAux nodes target fuel lower middle
        | .gt => findNodeAux nodes target fuel (middle + 1) upper
    else
      none

/-- Find one stored node's dense row index in logarithmic comparisons. -/
@[inline] private def findNode? (nodes : Array NodeId) (target : NodeId) : Option Nat :=
  findNodeAux nodes target (nodes.size + 1) 0 nodes.size

/-- Reconstruct one incoming row by dense node index. -/
def incomingAt? [Ord R] (graph : Graph R) (index : Nat) : Option (Row R) := do
  let dependent ← graph.nodes[index]?
  let start ← graph.offsets[index]?
  let stop ← graph.offsets[index + 1]?
  let mut incoming := Array.emptyWithCapacity (stop - start)
  for edgeIndex in [start:stop] do
    let head ← graph.heads[edgeIndex]?
    let relation ← graph.relations[edgeIndex]?
    let origin ← graph.origins[edgeIndex]?
    incoming := incoming.push ⟨head, relation, origin⟩
  return ⟨dependent, incoming⟩

/-- Reconstruct one stored node's incoming row. -/
def incoming? [Ord R] (graph : Graph R) (dependent : NodeId) : Option (Row R) := do
  let index ← findNode? graph.nodes dependent
  graph.incomingAt? index

/-- Reconstruct every canonical incoming row from checked CSR storage. -/
def toRows [Ord R] (graph : Graph R) : Array (Row R) := Id.run do
  let mut rows := Array.emptyWithCapacity graph.nodeCount
  for index in [0:graph.nodeCount] do
    match graph.incomingAt? index with
    | some row => rows := rows.push row
    | none => pure ()
  return rows

/-- Map relations and revalidate under an explicit budget; collisions become duplicate errors. -/
def mapRelationsWith [Ord R] [Ord S] (config : GraphConfig) (f : R → S)
    (graph : Graph R) : Except (GraphError S) (Graph S) :=
  ofRowsWith config <| graph.toRows.map fun row ↦
    { dependent := row.dependent
      incoming :=
        (row.incoming.map fun arc ↦ { arc with relation := f arc.relation }).mergeSort
          fun left right ↦
            compareArcKey left.head left.relation right.head right.relation == .lt }

/-- Map relations under production limits and revalidate canonical order and uniqueness. -/
@[inline] def mapRelations [Ord R] [Ord S] (f : R → S)
    (graph : Graph R) : Except (GraphError S) (Graph S) :=
  graph.mapRelationsWith .default f

end Graph

end Nlp.Dependency
