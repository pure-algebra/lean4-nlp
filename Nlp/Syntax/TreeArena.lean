import Nlp.Syntax.NamedTree

/-!
# Checked preorder arenas for named constituency trees

Tree queries should not repeatedly recurse through nested `Array` children.  `TreeArena` flattens
one nonempty `NamedTree` into preorder columns, a child CSR, sibling links, subtree intervals, and
terminal-yield intervals.  Construction uses an explicit work stack, enforces exact resource
limits before every retained entry, and seals the arrays behind a private checked constructor.
-/

namespace Nlp.Syntax

/-- A dense node position in one tree arena.  Every public lookup checks its bound. -/
abbrev TreeNodeId := Nat

/-- Whether one preorder node is a terminal form or a phrasal category. -/
inductive TreeNodeKind where
  | branch
  | leaf
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Exact resource limits for flattening one named tree. -/
structure TreeArenaConfig where
  /-- Maximum retained preorder nodes. -/
  maxNodes : Nat := 1_048_576
  /-- Maximum retained parent-to-child edges. -/
  maxEdges : Nat := 1_048_575
  /-- Maximum aggregate UTF-8 bytes across category labels and terminal forms. -/
  maxTextBytes : Nat := 67_108_864
  deriving Repr, DecidableEq, Inhabited

namespace TreeArenaConfig

/-- Production limits for one checked tree arena. -/
def default : TreeArenaConfig := {}

end TreeArenaConfig

/-- A deterministic resource or representation failure from tree-arena construction. -/
inductive TreeArenaError where
  | nodeBudget (required limit : Nat)
  | edgeBudget (required limit : Nat)
  | textBudget (required limit : Nat)
  | emptyArena
  | nodeColumn (column : String) (expected found : Nat)
  | yieldColumn (leaves forms : Nat)
  | offsetCount (expected found : Nat)
  | edgeCount (expected found : Nat)
  | invalidOffset (node start stop edges : Nat)
  | invalidRootParent
  | invalidParent (node parent nodes : Nat)
  | missingChild (node : Nat)
  | duplicateChild (node : Nat)
  | childParent (parent child : Nat) (stored : Option Nat)
  | childOrder (parent left right : Nat)
  | sibling (node : Nat) (left right expectedLeft expectedRight : Option Nat)
  | preorderSpan (node start stop nodes : Nat)
  | yieldSpan (node start stop leaves : Nat)
  | leafChildren (node start stop : Nat)
  | leafOrdinal (node ordinal : Nat)
  | leafForm (node ordinal : Nat)
  | branchChildren (node : Nat)
  | childPreorder (parent child expected : Nat)
  | childYield (parent child expected found : Nat)
  | rootPreorder (found expected : Nat)
  | rootYield (start stop expected : Nat)
  | sourceYield
  | sourceColumns
  deriving Repr, DecidableEq

/-- Constant-depth-stack work item for checking one source tree's terminal yield. -/
private inductive YieldCheckFrame where
  | enter (tree : NamedTree)
  | siblings (trees : Array NamedTree) (next : Nat)
  deriving Inhabited

/--
Check that an array is exactly a named tree's source-order terminal yield.

The checker visits source nodes with an explicit resume stack and compares leaves online, so it
does not recurse at hostile tree depth or allocate a second yield array.
-/
def checkNamedTreeYield (tree : NamedTree) (forms : Array String) : Bool := Id.run do
  let mut ordinal := 0
  let mut stack : Array YieldCheckFrame := #[.enter tree]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .siblings trees next =>
        if next < trees.size then
          stack := stack.push (.siblings trees (next + 1))
          stack := stack.push (.enter trees[next]!)
    | .enter current =>
        match current with
        | .leaf form =>
            unless forms[ordinal]? = some form do
              return false
            ordinal := ordinal + 1
        | .node _ first rest =>
            stack := stack.push (.siblings rest 0)
            stack := stack.push (.enter first)
  return ordinal = forms.size

/-- Constant-depth-stack item for checking every flat column against the source tree. -/
private inductive SourceCheckFrame where
  | enter (tree : NamedTree) (parent : Option (TreeNodeId × Nat))
  | siblings (parent : TreeNodeId) (trees : Array NamedTree) (next : Nat)
  | exit (node : TreeNodeId)
  deriving Inhabited

/--
Check exact source correspondence for labels, kinds, parents, child preorder, and both spans.

The explicit resume stack retains one pending child per active depth. Leaves are checked online
against the terminal-node and terminal-form columns, so no second flattened tree is allocated.
-/
def checkNamedTreeColumns (tree : NamedTree) (labels : Array String)
    (kinds : Array TreeNodeKind) (parents : Array (Option TreeNodeId))
    (childOffsets children subtreeStops yieldStarts yieldStops leafNodes : Array Nat)
    (yieldForms : Array String) : Bool := Id.run do
  let mut nextNode := 0
  let mut nextLeaf := 0
  let mut stack : Array SourceCheckFrame := #[.enter tree none]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .exit node =>
        unless subtreeStops[node]? = some nextNode do return false
        unless yieldStops[node]? = some nextLeaf do return false
    | .siblings parent rest next =>
        if next < rest.size then
          stack := stack.push (.siblings parent rest (next + 1))
          stack := stack.push (.enter rest[next]! (some (parent, next + 1)))
    | .enter current parentSlot =>
        let node := nextNode
        nextNode := nextNode + 1
        unless node < labels.size do return false
        unless parents[node]? = some (parentSlot.map Prod.fst) do return false
        match parentSlot with
        | none => pure ()
        | some (parent, ordinal) =>
            let start := childOffsets[parent]?.getD children.size
            unless children[start + ordinal]? = some node do return false
        unless yieldStarts[node]? = some nextLeaf do return false
        let start := childOffsets[node]?.getD (children.size + 1)
        let stop := childOffsets[node + 1]?.getD (children.size + 1)
        match current with
        | .leaf form =>
            unless labels[node]? = some form && kinds[node]? = some .leaf do return false
            unless start = stop do return false
            unless subtreeStops[node]? = some (node + 1) do return false
            unless yieldStops[node]? = some (nextLeaf + 1) do return false
            unless leafNodes[nextLeaf]? = some node do return false
            unless yieldForms[nextLeaf]? = some form do return false
            nextLeaf := nextLeaf + 1
        | .node category first rest =>
            unless labels[node]? = some category && kinds[node]? = some .branch do
              return false
            unless stop = start + rest.size + 1 do return false
            stack := stack.push (.exit node)
            stack := stack.push (.siblings node rest 0)
            stack := stack.push (.enter first (some (node, 0)))
  return nextNode = labels.size && nextLeaf = yieldForms.size &&
    leafNodes.size = yieldForms.size

/-- Validate all aligned preorder, child, sibling, subtree, and yield columns. -/
private def checkStorage (labels : Array String) (kinds : Array TreeNodeKind)
    (parents leftSiblings rightSiblings : Array (Option TreeNodeId))
    (childOffsets children subtreeStops yieldStarts yieldStops leafNodes : Array Nat)
    (yieldForms : Array String) : Except TreeArenaError Unit := do
  let nodes := labels.size
  if nodes = 0 then
    throw .emptyArena
  unless kinds.size = nodes do
    throw <| .nodeColumn "kinds" nodes kinds.size
  unless parents.size = nodes do
    throw <| .nodeColumn "parents" nodes parents.size
  unless leftSiblings.size = nodes do
    throw <| .nodeColumn "leftSiblings" nodes leftSiblings.size
  unless rightSiblings.size = nodes do
    throw <| .nodeColumn "rightSiblings" nodes rightSiblings.size
  unless subtreeStops.size = nodes do
    throw <| .nodeColumn "subtreeStops" nodes subtreeStops.size
  unless yieldStarts.size = nodes do
    throw <| .nodeColumn "yieldStarts" nodes yieldStarts.size
  unless yieldStops.size = nodes do
    throw <| .nodeColumn "yieldStops" nodes yieldStops.size
  unless leafNodes.size = yieldForms.size do
    throw <| .yieldColumn leafNodes.size yieldForms.size
  unless childOffsets.size = nodes + 1 do
    throw <| .offsetCount (nodes + 1) childOffsets.size
  unless children.size = nodes - 1 do
    throw <| .edgeCount (nodes - 1) children.size
  unless childOffsets[0]? = some 0 do
    throw <| .invalidOffset 0 (childOffsets[0]?.getD 0)
      (childOffsets[1]?.getD 0) children.size
  unless parents[0]? = some none do
    throw .invalidRootParent
  let leaves := yieldForms.size
  let mut seen := Array.replicate nodes false
  for node in [0:nodes] do
    let parent := parents[node]!
    if node = 0 then
      unless parent.isNone do
        throw .invalidRootParent
    else
      match parent with
      | some parentNode =>
          unless parentNode < node && parentNode < nodes do
            throw <| .invalidParent node parentNode nodes
      | none => throw <| .missingChild node
    let start := childOffsets[node]!
    let stop := childOffsets[node + 1]!
    unless start <= stop && stop <= children.size do
      throw <| .invalidOffset node start stop children.size
    let subtreeStop := subtreeStops[node]!
    unless node < subtreeStop && subtreeStop <= nodes do
      throw <| .preorderSpan node node subtreeStop nodes
    let yieldStart := yieldStarts[node]!
    let yieldStop := yieldStops[node]!
    unless yieldStart < yieldStop && yieldStop <= leaves do
      throw <| .yieldSpan node yieldStart yieldStop leaves
    let mut previousChild : Option Nat := none
    for edge in [start:stop] do
      let child := children[edge]!
      unless child < nodes && node < child do
        throw <| .invalidParent child node nodes
      if seen[child]! then
        throw <| .duplicateChild child
      seen := seen.set! child true
      unless parents[child]! = some node do
        throw <| .childParent node child parents[child]!
      match previousChild with
      | some previous =>
          unless previous < child do
            throw <| .childOrder node previous child
      | none => pure ()
      let expectedLeft := previousChild
      let expectedRight :=
        if edge + 1 < stop then some children[edge + 1]! else none
      unless leftSiblings[child]! = expectedLeft &&
          rightSiblings[child]! = expectedRight do
        throw <| .sibling child leftSiblings[child]! rightSiblings[child]!
          expectedLeft expectedRight
      previousChild := some child
    match kinds[node]! with
    | .leaf =>
        unless start = stop do
          throw <| .leafChildren node start stop
        unless subtreeStop = node + 1 do
          throw <| .preorderSpan node node subtreeStop nodes
        unless yieldStop = yieldStart + 1 && leafNodes[yieldStart]? = some node do
          throw <| .leafOrdinal node yieldStart
        unless yieldForms[yieldStart]? = labels[node]? do
          throw <| .leafForm node yieldStart
    | .branch =>
        unless start < stop do
          throw <| .branchChildren node
        let mut expectedPreorder := node + 1
        let mut expectedYield := yieldStart
        for edge in [start:stop] do
          let child := children[edge]!
          unless child = expectedPreorder do
            throw <| .childPreorder node child expectedPreorder
          unless yieldStarts[child]! = expectedYield do
            throw <| .childYield node child expectedYield yieldStarts[child]!
          expectedPreorder := subtreeStops[child]!
          expectedYield := yieldStops[child]!
        unless expectedPreorder = subtreeStop do
          throw <| .preorderSpan node node subtreeStop nodes
        unless expectedYield = yieldStop do
          throw <| .yieldSpan node yieldStart yieldStop leaves
  if seen[0]! then
    throw <| .duplicateChild 0
  for node in [1:nodes] do
    unless seen[node]! do
      throw <| .missingChild node
  unless childOffsets.back? = some children.size do
    throw <| .invalidOffset nodes (childOffsets.back?.getD 0)
      (childOffsets.back?.getD 0) children.size
  for ordinal in [0:leaves] do
    let node := leafNodes[ordinal]!
    unless node < nodes && kinds[node]! = .leaf do
      throw <| .leafOrdinal node ordinal
    unless labels[node]? = yieldForms[ordinal]? do
      throw <| .leafForm node ordinal
  unless subtreeStops[0]! = nodes do
    throw <| .rootPreorder subtreeStops[0]! nodes
  unless yieldStarts[0]! = 0 && yieldStops[0]! = leaves do
    throw <| .rootYield yieldStarts[0]! yieldStops[0]! leaves

/--
A checked, nonempty named tree in preorder and child-CSR form.

Every representation column is private.  Safe public accessors return `Option` for caller-selected
node and leaf ordinals; construction is the only way to obtain a value.
-/
structure TreeArena where
  private mk ::
  private sourceRoot : NamedTree
  private labels : Array String
  private kinds : Array TreeNodeKind
  private parents : Array (Option TreeNodeId)
  private leftSiblings : Array (Option TreeNodeId)
  private rightSiblings : Array (Option TreeNodeId)
  private childOffsets : Array Nat
  private children : Array TreeNodeId
  private subtreeStops : Array Nat
  private yieldStarts : Array Nat
  private yieldStops : Array Nat
  private leafNodes : Array TreeNodeId
  private yieldFormsRaw : Array String
  private checked : checkStorage labels kinds parents leftSiblings rightSiblings
    childOffsets children subtreeStops yieldStarts yieldStops leafNodes yieldFormsRaw = .ok ()
  private rootPreorder : subtreeStops[0]? = some labels.size
  private rootYieldStart : yieldStarts[0]? = some 0
  private rootYieldStop : yieldStops[0]? = some yieldFormsRaw.size
  private sourceYieldProof : checkNamedTreeYield sourceRoot yieldFormsRaw = true
  private sourceColumnsProof : checkNamedTreeColumns sourceRoot labels kinds parents childOffsets
    children subtreeStops yieldStarts yieldStops leafNodes yieldFormsRaw = true

/-- A sealed arena paired with proof of the exact source tree retained by construction. -/
structure TreeArenaBuild (source : NamedTree) where
  arena : TreeArena
  private source_eq : arena.sourceRoot = source

namespace TreeArena

/-- An explicit construction-stack item; exit frames close subtree and yield intervals. -/
private inductive Frame where
  | enter (tree : NamedTree) (parent : Option TreeNodeId)
  | siblings (parent : TreeNodeId) (trees : Array NamedTree) (next : Nat)
  | exit (node : TreeNodeId)
  deriving Inhabited

/-- Seal validated raw arrays and retain constant-time root interval witnesses. -/
private def sealArena (source : NamedTree) (labels : Array String)
    (kinds : Array TreeNodeKind)
    (parents leftSiblings rightSiblings : Array (Option TreeNodeId))
    (childOffsets children subtreeStops yieldStarts yieldStops leafNodes : Array Nat)
    (yieldForms : Array String) : Except TreeArenaError (TreeArenaBuild source) :=
  match checked : checkStorage labels kinds parents leftSiblings rightSiblings
      childOffsets children subtreeStops yieldStarts yieldStops leafNodes yieldForms with
  | .error cause => .error cause
  | .ok () =>
      if rootPreorder : subtreeStops[0]? = some labels.size then
        if rootYieldStart : yieldStarts[0]? = some 0 then
          if rootYieldStop : yieldStops[0]? = some yieldForms.size then
            if sourceYieldChecked : checkNamedTreeYield source yieldForms = true then
              if sourceColumnsChecked : checkNamedTreeColumns source labels kinds parents
                  childOffsets children subtreeStops yieldStarts yieldStops leafNodes
                  yieldForms = true then
                let arena := TreeArena.mk source labels kinds parents leftSiblings rightSiblings
                  childOffsets children subtreeStops yieldStarts yieldStops leafNodes yieldForms
                  checked rootPreorder rootYieldStart rootYieldStop sourceYieldChecked
                  sourceColumnsChecked
                .ok ⟨arena, rfl⟩
              else
                .error .sourceColumns
            else
              .error .sourceYield
          else
            .error <| .rootYield (yieldStarts[0]?.getD 0)
              (yieldStops[0]?.getD 0) yieldForms.size
        else
          .error <| .rootYield (yieldStarts[0]?.getD 0)
            (yieldStops[0]?.getD 0) yieldForms.size
      else
        .error <| .rootPreorder (subtreeStops[0]?.getD 0) labels.size

/-- Flatten one named tree and retain an exact, allocation-free source correspondence witness. -/
def buildNamedTreeWith (config : TreeArenaConfig) (tree : NamedTree) :
    Except TreeArenaError (TreeArenaBuild tree) := do
  let mut labels : Array String := #[]
  let mut kinds : Array TreeNodeKind := #[]
  let mut parents : Array (Option TreeNodeId) := #[]
  let mut subtreeStops : Array Nat := #[]
  let mut yieldStarts : Array Nat := #[]
  let mut yieldStops : Array Nat := #[]
  let mut leafNodes : Array TreeNodeId := #[]
  let mut yieldForms : Array String := #[]
  let mut textBytes := 0
  let mut edges := 0
  let mut stack : Array Frame := #[.enter tree none]
  while !stack.isEmpty do
    let frame := stack.back!
    stack := stack.pop
    match frame with
    | .exit node =>
        subtreeStops := subtreeStops.set! node labels.size
        yieldStops := yieldStops.set! node yieldForms.size
    | .siblings parent trees next =>
        if next < trees.size then
          stack := stack.push (.siblings parent trees (next + 1))
          stack := stack.push (.enter trees[next]! (some parent))
    | .enter current parent =>
        let requiredNodes := labels.size + 1
        if config.maxNodes < requiredNodes then
          throw <| .nodeBudget requiredNodes config.maxNodes
        if parent.isSome then
          let requiredEdges := edges + 1
          if config.maxEdges < requiredEdges then
            throw <| .edgeBudget requiredEdges config.maxEdges
          edges := requiredEdges
        let label := match current with
          | .leaf form => form
          | .node category _ _ => category
        let requiredTextBytes := textBytes + label.utf8ByteSize
        if config.maxTextBytes < requiredTextBytes then
          throw <| .textBudget requiredTextBytes config.maxTextBytes
        textBytes := requiredTextBytes
        let node := labels.size
        labels := labels.push label
        parents := parents.push parent
        subtreeStops := subtreeStops.push 0
        yieldStarts := yieldStarts.push yieldForms.size
        yieldStops := yieldStops.push 0
        match current with
        | .leaf form =>
            kinds := kinds.push .leaf
            leafNodes := leafNodes.push node
            yieldForms := yieldForms.push form
            subtreeStops := subtreeStops.set! node (node + 1)
            yieldStops := yieldStops.set! node yieldForms.size
        | .node _ first rest =>
            kinds := kinds.push .branch
            stack := stack.push (.exit node)
            stack := stack.push (.siblings node rest 0)
            stack := stack.push (.enter first (some node))
  let nodes := labels.size
  let mut degrees := Array.replicate nodes 0
  for node in [1:nodes] do
    match parents[node]! with
    | some parent => degrees := degrees.set! parent (degrees[parent]! + 1)
    | none => pure ()
  let mut childOffsets := Array.emptyWithCapacity (nodes + 1)
  let mut nextOffset := 0
  childOffsets := childOffsets.push 0
  for degree in degrees do
    nextOffset := nextOffset + degree
    childOffsets := childOffsets.push nextOffset
  let mut cursors := Array.emptyWithCapacity nodes
  for node in [0:nodes] do
    cursors := cursors.push childOffsets[node]!
  let mut children := Array.replicate edges 0
  let mut leftSiblings : Array (Option TreeNodeId) := Array.replicate nodes none
  let mut rightSiblings : Array (Option TreeNodeId) := Array.replicate nodes none
  for child in [1:nodes] do
    match parents[child]! with
    | none => pure ()
    | some parent =>
        let slot := cursors[parent]!
        if childOffsets[parent]! < slot then
          let left := children[slot - 1]!
          leftSiblings := leftSiblings.set! child (some left)
          rightSiblings := rightSiblings.set! left (some child)
        children := children.set! slot child
        cursors := cursors.set! parent (slot + 1)
  sealArena tree labels kinds parents leftSiblings rightSiblings childOffsets children
    subtreeStops yieldStarts yieldStops leafNodes yieldForms

/-- Flatten one named tree under exact node, edge, and UTF-8 text limits. -/
def ofNamedTreeWith (config : TreeArenaConfig) (tree : NamedTree) :
    Except TreeArenaError TreeArena :=
  match buildNamedTreeWith config tree with
  | .ok built => .ok built.arena
  | .error cause => .error cause

/-- Build with production limits while retaining the exact source-tree witness. -/
@[inline] def buildNamedTree (tree : NamedTree) : Except TreeArenaError (TreeArenaBuild tree) :=
  buildNamedTreeWith .default tree

/-- Flatten one named tree under production resource limits. -/
@[inline] def ofNamedTree (tree : NamedTree) : Except TreeArenaError TreeArena :=
  ofNamedTreeWith .default tree

/-- Re-run the complete executable representation checker. -/
def check (arena : TreeArena) : Except TreeArenaError Unit :=
  checkStorage arena.labels arena.kinds arena.parents arena.leftSiblings arena.rightSiblings
    arena.childOffsets arena.children arena.subtreeStops arena.yieldStarts arena.yieldStops
    arena.leafNodes arena.yieldFormsRaw

/-- Executable semantic well-formedness of a sealed tree arena. -/
def WF (arena : TreeArena) : Prop := arena.check = .ok ()

/-- Every constructible tree arena passes the complete executable checker. -/
theorem wellFormed (arena : TreeArena) : arena.WF := arena.checked

/-- Exact immutable named tree from which this arena was constructed. -/
@[inline] def sourceTree (arena : TreeArena) : NamedTree := arena.sourceRoot

/-- Dense preorder node count. -/
@[inline] def nodeCount (arena : TreeArena) : Nat := arena.labels.size

/-- Retained immediate-child edge count. -/
@[inline] def edgeCount (arena : TreeArena) : Nat := arena.children.size

/-- Number of terminal forms in the tree yield. -/
@[inline] def leafCount (arena : TreeArena) : Nat := arena.yieldFormsRaw.size

/-- The unique root is preorder node zero. -/
@[inline] def root (_arena : TreeArena) : TreeNodeId := 0

/-- Validate a caller-selected preorder position. -/
@[inline] def nodeAt? (arena : TreeArena) (node : Nat) : Option TreeNodeId :=
  if node < arena.nodeCount then some node else none

/-- Node category or terminal form at one checked preorder position. -/
@[inline] def label? (arena : TreeArena) (node : TreeNodeId) : Option String :=
  arena.labels[node]?

/-- Whether one checked node is a branch or terminal leaf. -/
@[inline] def kind? (arena : TreeArena) (node : TreeNodeId) : Option TreeNodeKind :=
  arena.kinds[node]?

/-- Parent lookup that distinguishes a root from an invalid node. -/
@[inline] def parentAt? (arena : TreeArena) (node : TreeNodeId) :
    Option (Option TreeNodeId) :=
  arena.parents[node]?

/-- Parent of a non-root node; root and invalid positions return `none`. -/
@[inline] def parent? (arena : TreeArena) (node : TreeNodeId) : Option TreeNodeId :=
  (arena.parentAt? node).join

/-- Immediate left sibling of a checked node. -/
@[inline] def leftSibling? (arena : TreeArena) (node : TreeNodeId) : Option TreeNodeId :=
  (arena.leftSiblings[node]?).join

/-- Immediate right sibling of a checked node. -/
@[inline] def rightSibling? (arena : TreeArena) (node : TreeNodeId) : Option TreeNodeId :=
  (arena.rightSiblings[node]?).join

/-- Half-open range in the arena's private flat child column. -/
def childRange? (arena : TreeArena) (node : TreeNodeId) : Option (Nat × Nat) := do
  let start <- arena.childOffsets[node]?
  let stop <- arena.childOffsets[node + 1]?
  return (start, stop)

/-- Read one immediate child by zero-based ordinal within its parent row. -/
def childAt? (arena : TreeArena) (node ordinal : Nat) : Option TreeNodeId := do
  let (start, stop) <- arena.childRange? node
  if start + ordinal < stop then arena.children[start + ordinal]? else none

/-- Reconstruct one checked node's immediate children in source order. -/
def childrenOf? (arena : TreeArena) (node : TreeNodeId) : Option (Array TreeNodeId) := do
  let (start, stop) <- arena.childRange? node
  let mut output := Array.emptyWithCapacity (stop - start)
  for edge in [start:stop] do
    let child <- arena.children[edge]?
    output := output.push child
  return output

/-- Half-open preorder interval occupied by one complete subtree. -/
def preorderSpan? (arena : TreeArena) (node : TreeNodeId) : Option (Nat × Nat) := do
  let stop <- arena.subtreeStops[node]?
  return (node, stop)

/-- Half-open terminal-yield interval covered by one node. -/
def yieldSpan? (arena : TreeArena) (node : TreeNodeId) : Option (Nat × Nat) := do
  let start <- arena.yieldStarts[node]?
  let stop <- arena.yieldStops[node]?
  return (start, stop)

/-- Terminal preorder node at one yield ordinal. -/
@[inline] def leafNode? (arena : TreeArena) (ordinal : Nat) : Option TreeNodeId :=
  arena.leafNodes[ordinal]?

/-- Terminal form at one yield ordinal. -/
@[inline] def yieldForm? (arena : TreeArena) (ordinal : Nat) : Option String :=
  arena.yieldFormsRaw[ordinal]?

/-- Complete source-order terminal yield. -/
@[inline] def yieldForms (arena : TreeArena) : Array String := arena.yieldFormsRaw

/-- Aggregate UTF-8 bytes across every category label and terminal form column entry. -/
def labelBytes (arena : TreeArena) : Nat :=
  arena.labels.foldl (fun total label => total + label.utf8ByteSize) 0

/-- The retained flattened yield passed an exact iterative check against the source tree. -/
theorem sourceYieldChecked (arena : TreeArena) :
    checkNamedTreeYield arena.sourceTree arena.yieldForms = true :=
  arena.sourceYieldProof

/-- Re-run the complete iterative source-to-flat-column correspondence checker. -/
def checkSourceColumns (arena : TreeArena) : Bool :=
  checkNamedTreeColumns arena.sourceRoot arena.labels arena.kinds arena.parents
    arena.childOffsets arena.children arena.subtreeStops arena.yieldStarts arena.yieldStops
    arena.leafNodes arena.yieldFormsRaw

/-- Every constructible arena exactly corresponds to its retained source tree in every column. -/
theorem sourceColumnsChecked (arena : TreeArena) : arena.checkSourceColumns = true :=
  arena.sourceColumnsProof

/-- Internal well-formedness and exact source-column correspondence hold together. -/
theorem sourceCorrespondence (arena : TreeArena) :
    arena.WF ∧ arena.checkSourceColumns = true :=
  ⟨arena.wellFormed, arena.sourceColumnsChecked⟩

/-- Dense node identifiers in deterministic preorder. -/
def preorder (arena : TreeArena) : Array TreeNodeId := Array.range arena.nodeCount

/-- The root covers every preorder node exactly once. -/
theorem root_preorderSpan (arena : TreeArena) :
    arena.preorderSpan? arena.root = some (0, arena.nodeCount) := by
  simp [preorderSpan?, root, nodeCount, arena.rootPreorder]

/-- The root covers the complete terminal yield. -/
theorem root_yieldSpan (arena : TreeArena) :
    arena.yieldSpan? arena.root = some (0, arena.leafCount) := by
  simp [yieldSpan?, root, leafCount, arena.rootYieldStart, arena.rootYieldStop]

end TreeArena

namespace TreeArenaBuild

/-- The build result retains the exact source tree without another traversal or copy. -/
theorem sourceTree_eq (built : TreeArenaBuild source) : built.arena.sourceTree = source :=
  built.source_eq

/-- The flattened yield passed an exact iterative check against the caller's source tree. -/
theorem sourceYieldChecked (built : TreeArenaBuild source) :
    checkNamedTreeYield source built.arena.yieldForms = true := by
  simpa only [sourceTree_eq built] using built.arena.sourceYieldChecked

/-- The built arena's complete flat representation matches the caller's exact source tree. -/
theorem sourceColumnsChecked (built : TreeArenaBuild source) :
    built.arena.checkSourceColumns = true ∧ built.arena.sourceTree = source :=
  ⟨built.arena.sourceColumnsChecked, sourceTree_eq built⟩

end TreeArenaBuild

end Nlp.Syntax
