import Init.Data.Dyadic.Basic
import Nlp.Core.Data.Dependency
import Nlp.Dependency.ArcScores

/-!
# Single-root nonprojective dependency arborescences

This module implements the dense form of Tarjan's refinement of the Chu--Liu--Edmonds
algorithm. Incoming-edge rows are indexed by original source vertices. Contracting a cycle merges
its rows once, so the kernel performs `O(n^2)` graph operations and retains `O(n^2)` slots.
Exact integer-operation cost additionally depends on the source exponent span and operand width.
`workspaceEntryCount` is the size-only baseline; `workspaceEntryCountFor` conservatively charges
the arbitrary-precision limbs required by a compiled graph before any dense row is allocated.

The artificial root participates in one run. Reduced weights are ordered lexicographically by the
number of artificial-root arcs and then by the exact dyadic values encoded by the source `Float`
bits, forcing a one-root analysis whenever one exists. Exact ties retain the lower original
`(dependent, head)` coordinates. Contraction remembers immediate original edges; a reconstruction
forest expands nested cycles. Results expose that exact objective separately from the optional
dependent-order IEEE-754 reporting fold.

Algorithmic sources:
* Chu and Liu's original shortest-arborescence algorithm:
  https://www.cs.cmu.edu/~15850/handouts/chu-liu_1965.pdf
* Edmonds' optimum-branching formulation: https://doi.org/10.6028/jres.071B.032
* Tarjan's dense `O(n^2)` branching refinement: https://doi.org/10.1002/net.3230070103
* Camerini--Fratta--Maffioli's reconstruction correction: https://doi.org/10.1002/net.3230090403
* The dependency-parsing reduction of McDonald et al.: https://aclanthology.org/H05-1066/
-/

namespace Nlp.Dependency.Arborescence

/-- Resource policy for one dense arborescence kernel. -/
structure KernelConfig where
  /--
  Maximum live machine-word-equivalent workspace entries. Exact source exponent spans can make
  the graph-specific requirement exceed the size-only `workspaceEntryCount` baseline.
  -/
  maxWorkspaceEntries : Nat := 67_108_864
  deriving Repr, DecidableEq, Inhabited

namespace KernelConfig

/-- Production workspace policy for dense nonprojective inference. -/
def default : KernelConfig := {}

end KernelConfig

/-- A checked kernel failed for a reason other than the absence of a finite analysis. -/
inductive KernelError where
  /-- The conservative live-workspace requirement exceeded the configured entry budget. -/
  | workspaceBudget (required limit : Nat)
  /-- A supposedly selected original arc was not available in the compiled table. -/
  | missingChoice (head dependent : Nat)
  /-- A finite arc violated the graph-wide exact binary scaling invariant. -/
  | invalidExactScale (head dependent commonShift valueShift : Nat)
  /-- Expansion assigned the same original dependent more than once. -/
  | duplicateDependent (dependent : Nat)
  /-- Expansion did not assign every original dependent. -/
  | incompleteExpansion (expected found : Nat)
  /-- A contraction or reconstruction-forest identifier violated an internal bound. -/
  | invalidIdentifier (kind : String) (identifier bound : Nat)
  /-- A selected-parent chain did not close at its advertised cycle root. -/
  | malformedCycle (component : Nat)
  /-- A reconstruction leaf did not reach the selected forest root. -/
  | malformedReconstruction (edge dependent : Nat)
  /-- Checked expansion exposed a structural bug in the kernel. -/
  | invalidTree (cause : TreeError)
  deriving Repr

/-- Exact labeled nonprojective dependency output in CoNLL-U head coordinates. -/
structure Result where
  private mk ::
  /-- `heads[i]` is the 1-based head of dependent `i + 1`; zero is artificial root. -/
  heads : Array Nat
  /-- Exact source ordinals in the compiled relation inventory. -/
  relations : Array UInt32
  /-- Exact sum of the selected source binary64 arc values. -/
  exactCost : Dyadic
  /-- Dependent-order IEEE-754 fold, or `none` when that reporting fold overflows. -/
  reportedCost? : Option Float
  /-- Heads and relation ordinals are positionally aligned. -/
  aligned : relations.size = heads.size
  /-- Expanded heads form a checked general dependency tree. -/
  wellFormed : SentenceTreeWF heads
  /-- Exactly one dependent is attached directly to the artificial root. -/
  singleRoot : heads.count 0 = 1
  /-- Every available operational report is finite. -/
  reportedFinite :
    match reportedCost? with
    | none => True
    | some value => value.isFinite = true

/-- Named view of one checked nonprojective dependency result. -/
structure NamedResult where
  private mk ::
  /-- CoNLL-U-coordinate dependency heads. -/
  heads : Array Nat
  /-- Caller-supplied relation names aligned with `heads`. -/
  relations : Array String
  /-- Exact sum of the selected source binary64 arc values. -/
  exactCost : Dyadic
  /-- Dependent-order IEEE-754 fold, or `none` when that reporting fold overflows. -/
  reportedCost? : Option Float
  /-- Heads and relation names are positionally aligned. -/
  aligned : relations.size = heads.size
  /-- Expanded heads form a checked general dependency tree. -/
  wellFormed : SentenceTreeWF heads
  /-- Exactly one dependent is attached directly to the artificial root. -/
  singleRoot : heads.count 0 = 1
  /-- Every available operational report is finite. -/
  reportedFinite :
    match reportedCost? with
    | none => True
    | some value => value.isFinite = true

/-- Exact lexicographic reduced weight used to encode one root without a big-M constant. -/
private structure Weight where
  rootArcs : Int
  cost : Int

/-- One dense incoming-edge row and the weight currently subtracted from every valid cell. -/
private structure Row where
  roots : Array Int
  costs : Array Int
  dependents : Array UInt32
  offset : Weight

/-- A candidate retains both stored and reduced weights plus its original source coordinates. -/
private structure Candidate where
  stored : Weight
  reduced : Weight
  head : Nat
  dependent : Nat

/-- One original edge chosen before reconstruction removes superseded cycle edges. -/
private structure PickedEdge where
  head : Nat
  dependent : Nat

/-- Live conceptual workspace consumption under one explicit limit. -/
private structure Budget where
  used : Nat
  limit : Nat

/-- Maximum number of original or contracted vertex identifiers needed for `n` real tokens. -/
@[inline] private def maxNodeCount (n : Nat) : Nat :=
  if n = 0 then 1 else 2 * n

/-- Conceptual entries retained by one live dense incoming-edge row. -/
@[inline] private def rowWorkspaceEntries (originalNodes : Nat) : Nat :=
  3 * originalNodes + 2

/-- Fixed and initial dense-row entries retained before the first edge is selected. -/
@[inline] private def initialWorkspaceEntryCount (n : Nat) : Nat :=
  let originalNodes := n + 1
  let nodes := maxNodeCount n
  7 * nodes + 4 * originalNodes + n * rowWorkspaceEntries originalNodes

/-- Baseline live-entry bound before graph-specific exact-integer limb accounting. -/
@[inline] def workspaceEntryCount (n : Nat) : Nat :=
  let originalNodes := n + 1
  let nodes := maxNodeCount n
  initialWorkspaceEntryCount n + 4 * nodes + rowWorkspaceEntries originalNodes + n

/-- Reserve conceptual entries before allocating them. -/
private def Budget.reserve (budget : Budget) (count : Nat) : Except KernelError Budget :=
  let required := budget.used + count
  if budget.limit < required then
    .error (.workspaceBudget required budget.limit)
  else
    .ok { budget with used := required }

/-- Release conceptual entries whose owning arrays have been cleared. -/
@[inline] private def Budget.release (budget : Budget) (count : Nat) : Budget :=
  { budget with used := budget.used - count }

/-- The additive identity for a row offset. -/
private def zeroWeight : Weight := ⟨0, 0⟩

/-- A row holding no incoming original edges. -/
private def emptyRow : Row := ⟨#[], #[], #[], zeroWeight⟩

/-- Strict lexicographic comparison of root count followed by exact scaled cost. -/
@[inline] private def weightLess (left right : Weight) : Bool :=
  if left.rootArcs < right.rootArcs then
    true
  else if right.rootArcs < left.rootArcs then
    false
  else
    decide (left.cost < right.cost)

/-- Prefer lower reduced weight, then lower original dependent and head coordinates. -/
@[inline] private def candidateBetter (left right : Candidate) : Bool :=
  if weightLess left.reduced right.reduced then
    true
  else if weightLess right.reduced left.reduced then
    false
  else if left.dependent < right.dependent then
    true
  else
    left.dependent = right.dependent && left.head < right.head

/-- Odd coefficient and biased binary shift of one finite nonnegative binary64 value. -/
private structure BinaryCost where
  coefficient : Nat
  shift : Nat

/-- Decode a finite nonnegative binary64 value as `coefficient * 2^(shift - 1074)`. -/
@[inline] private def decodeBinaryCost (value : Float) : BinaryCost :=
  let bits := value.toBits
  let exponent := ((bits >>> 52) &&& 0x7ff).toNat
  let fraction := (bits &&& 0x000fffffffffffff).toNat
  let rawCoefficient := if exponent = 0 then fraction else (2 ^ 52 : Nat) + fraction
  if rawCoefficient = 0 then
    ⟨0, 0⟩
  else
    let zeros := (rawCoefficient ^^^ (rawCoefficient - 1)).log2
    let baseShift := if exponent = 0 then 0 else exponent - 1
    ⟨rawCoefficient >>> zeros, baseShift + zeros⟩

/-- Scale range and largest normalized source coefficient discovered before row allocation. -/
private structure ExactScale where
  minimumShift : Nat
  maximumShift : Nat
  coefficientBits : Nat

/-- Scan finite source costs once to choose and budget their common exact integer unit. -/
private def exactScale (arcs : ArcScores) : ExactScale := Id.run do
  let originalNodes := arcs.n + 1
  let mut minimum : Option Nat := none
  let mut maximum := 0
  let mut coefficientBits := 0
  for dependent in [1:originalNodes] do
    for head in [0:originalNodes] do
      if let some choice := arcs.choice? head dependent then
        let decoded := decodeBinaryCost choice.cost
        unless decoded.coefficient = 0 do
          minimum := some <| minimum.map (min decoded.shift) |>.getD decoded.shift
          maximum := max maximum decoded.shift
          coefficientBits := max coefficientBits (decoded.coefficient.log2 + 1)
  return ⟨minimum.getD 0, maximum, coefficientBits⟩

/-- Conservative bit width of any exact reduced operand retained by this graph. -/
private def exactOperandBits (n : Nat) (scale : ExactScale) : Nat :=
  let sourceBits := max 1 (scale.coefficientBits + (scale.maximumShift - scale.minimumShift))
  sourceBits + (max n 1).log2 + 2

/-- Maximum number of exact row cells and row offsets simultaneously live. -/
private def exactCostSlotCount (n : Nat) : Nat :=
  (n + 1) * (n + 2) + 8

/-- Conservative object, descriptor, and allocation-metadata words for one boxed integer. -/
private def bigIntOverheadWords : Nat := 4

/-- Extra machine words per exact cost after its baseline array slot. -/
private def extraExactWordsPerCost (operandBits : Nat) : Nat :=
  if operandBits ≤ 60 then
    0
  else
    let limbWords := (operandBits + 63) / 64
    limbWords + bigIntOverheadWords

/-- Graph-specific workspace including conservative variable-width exact-integer storage. -/
private def workspaceEntryCountForScale (n : Nat) (scale : ExactScale) : Nat :=
  workspaceEntryCount n + exactCostSlotCount n * extraExactWordsPerCost (exactOperandBits n scale)

/-- Conservative graph-specific workspace requirement, including arbitrary-precision limbs. -/
def workspaceEntryCountFor (arcs : ArcScores) : Nat :=
  workspaceEntryCountForScale arcs.n (exactScale arcs)

/-- Scale one source cost into the graph-wide exact integer unit. -/
@[inline] private def exactUnits (commonShift head dependent : Nat) (value : Float) :
    Except KernelError Int := do
  let decoded := decodeBinaryCost value
  if decoded.coefficient = 0 then
    return 0
  unless commonShift ≤ decoded.shift do
    throw <| .invalidExactScale head dependent commonShift decoded.shift
  return Int.ofNat decoded.coefficient <<< (decoded.shift - commonShift)

/-- Subtract one row offset in the exact scaled-integer domain. -/
@[inline] private def reduceWeight (stored offset : Weight) : Weight :=
  ⟨stored.rootArcs - offset.rootArcs, stored.cost - offset.cost⟩

/-- Read one valid row cell and compute its current exact reduced weight. -/
private def Row.candidate? (row : Row) (head : Nat) : Option Candidate := do
  let dependent := (row.dependents.getD head 0).toNat
  if dependent = 0 then
    none
  else
    let stored : Weight := ⟨row.roots.getD head 0, row.costs.getD head 0⟩
    let reduced := reduceWeight stored row.offset
    some ⟨stored, reduced, head, dependent⟩

/-- Build the original incoming row for one real dependent. -/
private def originalRow (arcs : ArcScores) (commonShift dependent : Nat) :
    Except KernelError Row := do
  let originalNodes := arcs.n + 1
  let mut roots := Array.replicate originalNodes 0
  let mut costs : Array Int := Array.replicate originalNodes 0
  let mut dependents := Array.replicate originalNodes 0
  for head in [0:originalNodes] do
    if let some choice := arcs.choice? head dependent then
      let units ← exactUnits commonShift head dependent choice.cost
      roots := roots.set! head (if head = 0 then 1 else 0)
      costs := costs.set! head units
      dependents := dependents.set! head (UInt32.ofNat dependent)
  return ⟨roots, costs, dependents, zeroWeight⟩

/-- Select the best external original edge entering one current component. -/
private def selectIncoming (row : Row) (componentOfOriginal : Array Nat)
    (targetComponent : Nat) : Option Candidate := Id.run do
  let mut best : Option Candidate := none
  for head in [0:componentOfOriginal.size] do
    unless componentOfOriginal.getD head targetComponent = targetComponent do
      if let some candidate := row.candidate? head then
        match best with
        | none => best := some candidate
        | some previous =>
            if candidateBetter candidate previous then
              best := some candidate
  return best

/-- Merge all normalized cycle rows, retaining one best edge for every original source. -/
private def mergeCycleRows (originalNodes : Nat) (rows : Array Row)
    (cycle : Array Nat) : Row := Id.run do
  let mut roots := Array.replicate originalNodes 0
  let mut costs : Array Int := Array.replicate originalNodes 0
  let mut dependents := Array.replicate originalNodes 0
  for head in [0:originalNodes] do
    let mut best : Option Candidate := none
    for component in cycle do
      let row := rows.getD component emptyRow
      if let some candidate := row.candidate? head then
        match best with
        | none => best := some candidate
        | some previous =>
            if candidateBetter candidate previous then
              best := some candidate
    if let some candidate := best then
      roots := roots.set! head candidate.reduced.rootArcs
      costs := costs.set! head candidate.reduced.cost
      dependents := dependents.set! head (UInt32.ofNat candidate.dependent)
  return ⟨roots, costs, dependents, zeroWeight⟩

/-- Resolve weak connectivity while preserving path compression. -/
private def weakConnected (sets : Nlp.UnionFind) (left right : Nat) :
    Except KernelError (Bool × Nlp.UnionFind) :=
  match sets.connected left right with
  | some result => .ok result
  | none => .error (.invalidIdentifier "weak component" (max left right) sets.size)

/-- Join weak components or report a checked identifier failure. -/
private def weakUnion (sets : Nlp.UnionFind) (left right : Nat) :
    Except KernelError Nlp.UnionFind :=
  match sets.union left right with
  | some joined => .ok joined
  | none => .error (.invalidIdentifier "weak union" (max left right) sets.size)

/-- Count assignments without allocating an intermediate filtered array. -/
private def assignmentCount (assigned : Array Bool) : Nat :=
  assigned.foldl (init := 0) fun count value ↦ if value then count + 1 else count

/--
Run dense single-root Chu--Liu--Edmonds inference under an explicit live-workspace budget.

`none` means no finite one-root dependency tree exists. Workspace and checked expansion failures
remain explicit in `KernelError` and are never conflated with absent analysis.
-/
def parseWith? (config : KernelConfig) (arcs : ArcScores) :
    Except KernelError (Option Result) := do
  if arcs.n = 0 then
    return none
  let originalNodes := arcs.n + 1
  let maxNodes := maxNodeCount arcs.n
  let initialWorkspace := initialWorkspaceEntryCount arcs.n
  let baselineWorkspace := workspaceEntryCount arcs.n
  if config.maxWorkspaceEntries < baselineWorkspace then
    throw <| .workspaceBudget baselineWorkspace config.maxWorkspaceEntries
  let scale := exactScale arcs
  let requiredWorkspace := workspaceEntryCountForScale arcs.n scale
  if config.maxWorkspaceEntries < requiredWorkspace then
    throw <| .workspaceBudget requiredWorkspace config.maxWorkspaceEntries
  let rowEntries := rowWorkspaceEntries originalNodes
  let commonShift := scale.minimumShift
  let mut budget : Budget := ⟨initialWorkspace, config.maxWorkspaceEntries⟩
  let mut rows := Array.replicate maxNodes emptyRow
  for dependent in [1:originalNodes] do
    let row ← originalRow arcs commonShift dependent
    rows := rows.set! dependent row
  let mut active := (Array.replicate maxNodes false).set! 0 true
  for dependent in [1:originalNodes] do
    active := active.set! dependent true
  let mut componentOfOriginal := Array.range originalNodes
  let mut weak := Nlp.UnionFind.empty maxNodes
  let mut chosenEdge : Array (Option Nat) := Array.replicate maxNodes none
  let mut pending : Array (Array Nat) := Array.replicate maxNodes #[]
  let mut cycleMark := Array.replicate maxNodes false
  let mut picked : Array PickedEdge := #[]
  let mut reconstructionParent : Array (Option Nat) := #[]
  let mut leaf : Array (Option Nat) := Array.replicate originalNodes none
  let mut nodeCount := originalNodes
  for targetComponent in [1:maxNodes] do
    if targetComponent < nodeCount && active.getD targetComponent false then
      let row := rows.getD targetComponent emptyRow
      let some selected := selectIncoming row componentOfOriginal targetComponent
        | return none
      let nextBudget ← budget.reserve 2
      budget := nextBudget
      let edgeId := picked.size
      picked := picked.push ⟨selected.head, selected.dependent⟩
      reconstructionParent := reconstructionParent.push none
      if leaf.getD selected.dependent none |>.isNone then
        leaf := leaf.set! selected.dependent (some edgeId)
      let frame := pending.getD targetComponent #[]
      for childEdge in frame do
        if childEdge < reconstructionParent.size &&
            (reconstructionParent.getD childEdge none).isNone then
          reconstructionParent := reconstructionParent.set! childEdge (some edgeId)
        else
          throw <| .invalidIdentifier "reconstruction parent" childEdge
            reconstructionParent.size
      budget := budget.release frame.size
      pending := pending.set! targetComponent #[]
      rows := rows.set! targetComponent { row with offset := selected.stored }
      chosenEdge := chosenEdge.set! targetComponent (some edgeId)
      let sourceComponent := componentOfOriginal.getD selected.head targetComponent
      let (closesCycle, compressed) ← weakConnected weak sourceComponent targetComponent
      weak := compressed
      if !closesCycle then
        weak ← weakUnion weak sourceComponent targetComponent
      else
        let mut cycle := #[targetComponent]
        let mut current := sourceComponent
        let mut closed := current == targetComponent
        for _step in [0:maxNodes] do
          if closed then
            break
          unless current < nodeCount && active.getD current false do
            throw <| .malformedCycle current
          cycle := cycle.push current
          let some parentEdge := chosenEdge.getD current none
            | throw <| .malformedCycle current
          let parent := picked.getD parentEdge ⟨originalNodes, originalNodes⟩
          unless parent.head < originalNodes do
            throw <| .invalidIdentifier "cycle source" parent.head originalNodes
          current := componentOfOriginal.getD parent.head current
          closed := current == targetComponent
        unless closed && 2 ≤ cycle.size do
          throw <| .malformedCycle targetComponent
        unless nodeCount < maxNodes do
          throw <| .invalidIdentifier "contracted component" nodeCount maxNodes
        let newComponent := nodeCount
        let mergeBudget ← budget.reserve rowEntries
        budget := mergeBudget
        let frameBudget ← budget.reserve cycle.size
        budget := frameBudget
        let merged := mergeCycleRows originalNodes rows cycle
        let mut nextFrame := Array.emptyWithCapacity cycle.size
        for component in cycle do
          let some cycleEdge := chosenEdge.getD component none
            | throw <| .malformedCycle component
          nextFrame := nextFrame.push cycleEdge
          cycleMark := cycleMark.set! component true
        for original in [0:originalNodes] do
          let component := componentOfOriginal.getD original maxNodes
          if cycleMark.getD component false then
            componentOfOriginal := componentOfOriginal.set! original newComponent
        for component in cycle do
          active := active.set! component false
          rows := rows.set! component emptyRow
          cycleMark := cycleMark.set! component false
        budget := budget.release (cycle.size * rowEntries)
        rows := rows.set! newComponent merged
        active := active.set! newComponent true
        pending := pending.set! newComponent nextFrame
        weak ← weakUnion weak newComponent targetComponent
        nodeCount := nodeCount + 1
  let reconstructionBudget ← budget.reserve (picked.size + arcs.n)
  budget := reconstructionBudget
  let mut removed := Array.replicate picked.size false
  let mut heads := Array.replicate arcs.n 0
  let mut assigned := Array.replicate arcs.n false
  for reverseOffset in [0:picked.size] do
    let selectedId := picked.size - reverseOffset - 1
    unless removed.getD selectedId true do
      let edge := picked.getD selectedId ⟨originalNodes, originalNodes⟩
      unless 1 ≤ edge.dependent && edge.dependent ≤ arcs.n && edge.head ≤ arcs.n do
        throw <| .invalidIdentifier "picked edge" (max edge.head edge.dependent) originalNodes
      let dependentIndex := edge.dependent - 1
      if assigned.getD dependentIndex true then
        throw <| .duplicateDependent edge.dependent
      heads := heads.set! dependentIndex edge.head
      assigned := assigned.set! dependentIndex true
      let some firstLeaf := leaf.getD edge.dependent none
        | throw <| .malformedReconstruction selectedId edge.dependent
      let mut path := firstLeaf
      let mut reached := false
      for _step in [0:picked.size + 1] do
        unless path < picked.size && !removed.getD path true do
          throw <| .malformedReconstruction selectedId edge.dependent
        removed := removed.set! path true
        if path = selectedId then
          reached := true
          break
        let some parent := reconstructionParent.getD path none
          | throw <| .malformedReconstruction selectedId edge.dependent
        path := parent
      unless reached do
        throw <| .malformedReconstruction selectedId edge.dependent
  let found := assignmentCount assigned
  unless found = arcs.n do
    throw <| .incompleteExpansion arcs.n found
  if heads.count 0 != 1 then
    return none
  let mut relations := Array.replicate arcs.n arcs.rootRelation
  let mut exactTotal : Int := 0
  let mut reportedTotal := 0.0
  for index in [0:arcs.n] do
    let dependent := index + 1
    let head := heads.getD index dependent
    let some choice := arcs.choice? head dependent
      | throw <| .missingChoice head dependent
    relations := relations.set! index choice.relation
    exactTotal := exactTotal + (← exactUnits commonShift head dependent choice.cost)
    reportedTotal := reportedTotal + choice.cost
  let exactCost := Dyadic.ofIntWithPrec exactTotal (1074 - Int.ofNat commonShift)
  match Tree.ofArrays heads relations with
  | .error cause => throw <| .invalidTree cause
  | .ok tree =>
      if singleRoot : tree.heads.count 0 = 1 then
        if reportedFinite : reportedTotal.isFinite = true then
          return some <| .mk tree.heads tree.relations exactCost (some reportedTotal)
            tree.aligned tree.wellFormed singleRoot reportedFinite
        else
          return some <| .mk tree.heads tree.relations exactCost none tree.aligned
            tree.wellFormed singleRoot True.intro
      else
        return none

/-- Run dense single-root inference under the production workspace policy. -/
@[inline] def parse? (arcs : ArcScores) : Except KernelError (Option Result) :=
  parseWith? .default arcs

/-- Resolve every exact relation ordinal while preserving all checked tree properties. -/
def Result.resolve? (arcs : ArcScores) (result : Result) : Option NamedResult := do
  if result.heads.size != arcs.n || result.relations.size != arcs.n then none else pure ()
  let mut names := Array.emptyWithCapacity arcs.n
  for relation in result.relations do
    let name ← arcs.relationName? relation
    names := names.push name
  if aligned : names.size = result.heads.size then
    some <| .mk result.heads names result.exactCost result.reportedCost? aligned
      result.wellFormed result.singleRoot result.reportedFinite
  else
    none

/-- Parse and resolve exact relation names under an explicit workspace policy. -/
def parseNamedWith? (config : KernelConfig) (arcs : ArcScores) :
    Except KernelError (Option NamedResult) := do
  let result? ← parseWith? config arcs
  match result? with
  | none => return none
  | some result =>
      match result.resolve? arcs with
      | some named => return some named
      | none => throw <| .invalidIdentifier "relation ordinal" arcs.n arcs.relationNames.size

/-- Parse and resolve exact relation names under the production workspace policy. -/
@[inline] def parseNamed? (arcs : ArcScores) : Except KernelError (Option NamedResult) :=
  parseNamedWith? .default arcs

end Nlp.Dependency.Arborescence
