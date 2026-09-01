import Nlp.Core.Data.DependencyGraph

/-!
# Bounded English enhanced dependencies

This module implements a deliberately small, word-node-only subset of enhanced Universal
Dependencies. It retains every basic-tree arc, lexicalizes selected modifier and coordination
relations from direct marker children, and propagates a conjunct governor's incoming relation
for one direct coordination level. The rule vocabulary follows the enhanced-syntax overview at
<https://universaldependencies.org/u/overview/enhanced-syntax.html>.

The transformer does not implement outgoing argument sharing, controlled subjects, relative
references, ellipsis, empty nodes, copy nodes, or Enhanced++. Public range APIs read flattened
columns in place and return sentence-local graph node identifiers without allocating slices.
-/

namespace Nlp.Dependency.EnglishEnhanced

/-- Independent enhancement switches and exact retained-output limits. -/
structure Config where
  /-- Append direct `case` markers to `nmod` and `obl` relations. -/
  lexicalizeNominals : Bool := true
  /-- Append direct `mark` or `case` markers to `acl` and `advcl` relations. -/
  lexicalizeClauses : Bool := true
  /-- Append the selected direct `cc` marker to `conj` relations. -/
  lexicalizeConjunctions : Bool := true
  /-- Propagate a conjunct governor's incoming non-structural relation one direct level. -/
  propagateIncomingConj : Bool := true
  /-- Maximum number of derived enhancement candidates before graph construction. -/
  maxCandidates : Nat := 1_048_576
  /-- Maximum number of canonical graph edges, including retained basic edges. -/
  maxEdges : Nat := 1_048_576
  /-- Maximum aggregate UTF-8 bytes in materialized lexicalized relation labels. -/
  maxLexicalBytes : Nat := 16_777_216
  deriving Repr, DecidableEq, Inhabited

namespace Config

/-- Production English enhancement policy. -/
def default : Config := {}

end Config

/-- A full input column failed alignment, range, tree, or resource validation. -/
inductive Error where
  /-- The relation column does not align with the flattened head column. -/
  | relationCount (expected found : Nat)
  /-- The form column does not align with the flattened head column. -/
  | formCount (expected found : Nat)
  /-- The lemma column does not align with the flattened head column. -/
  | lemmaCount (expected found : Nat)
  /-- The POS column does not align with the flattened head column. -/
  | posCount (expected found : Nat)
  /-- A requested half-open range is reversed or escapes the full columns. -/
  | invalidRange (start stop available : Nat)
  /-- Sentence-local heads in the selected range do not form a checked tree. -/
  | invalidTree (cause : TreeError)
  /-- A basic relation is not a structurally safe enhanced-UD label. -/
  | invalidRelation (dependent : Nat) (relation : String)
  /-- A root head and the exact `root` relation label do not coincide. -/
  | rootRelationMismatch (dependent head : Nat) (relation : String)
  /-- Derived candidates exceed the exact caller-selected limit. -/
  | candidateBudget (required limit : Nat)
  /-- Basic and derived canonical edges exceed the exact caller-selected limit. -/
  | edgeBudget (required limit : Nat)
  /-- Materialized lexicalized relation labels exceed the exact UTF-8 byte limit. -/
  | lexicalBudget (required limit : Nat)
  /-- Canonical CSR construction rejected the emitted rows. -/
  | graph (cause : GraphError String)
  /-- The checked graph did not retain the exact predicted node and edge counts. -/
  | inconsistentGraphCounts (expectedNodes foundNodes expectedEdges foundEdges : Nat)
  deriving Repr

/-- Exact public counts by source rule family. -/
structure Counts where
  /-- Basic-tree edges retained without rewriting. -/
  basic : Nat
  /-- Edges whose relation gained a lexical marker suffix. -/
  lexicalized : Nat
  /-- Incoming governor relations propagated to conjuncts. -/
  propagated : Nat
  deriving Repr, DecidableEq, Inhabited

namespace Counts

/-- Number of derived enhancement candidates. -/
@[inline] def candidates (counts : Counts) : Nat :=
  counts.lexicalized + counts.propagated

/-- Exact number of canonical edges expected from this bounded transformer. -/
@[inline] def total (counts : Counts) : Nat :=
  counts.basic + counts.candidates

end Counts

/-- A checked enhanced graph with exact node and edge accounting. -/
structure Result where
  private mk ::
  /-- Canonical word-node enhanced graph. -/
  graph : Graph String
  /-- Counts of retained and derived edge families. -/
  counts : Counts
  /-- Every selected basic-tree word appears exactly once as a graph node. -/
  nodeCount_eq : graph.nodeCount = counts.basic
  /-- No generated candidate was lost or duplicated during canonical CSR construction. -/
  edgeCount_eq : graph.edgeCount = counts.total

/-- Compare a relation's universal prefix without allocating a split array. -/
@[inline] private def relationIs (relation expected : String) : Bool :=
  relation == expected || relation.startsWith (expected ++ ":")

/-- Structural relations excluded from incoming-conj propagation. -/
@[inline] private def propagationExcluded (relation : String) : Bool :=
  relationIs relation "conj" || relationIs relation "cc" ||
    relationIs relation "case" || relationIs relation "mark" ||
    relationIs relation "punct"

/-- Convert one positive sentence-local word position to its full-column index. -/
@[inline] private def globalIndex (start localIndex : Nat) : Nat :=
  start + localIndex - 1

/-- Validate all flattened columns before range-local access begins. -/
private def checkColumns (heads : Array Nat) (relations forms lemmas pos : Array String) :
    Except Error Unit := do
  unless relations.size = heads.size do
    throw <| .relationCount heads.size relations.size
  unless forms.size = heads.size do
    throw <| .formCount heads.size forms.size
  unless lemmas.size = heads.size do
    throw <| .lemmaCount heads.size lemmas.size
  unless pos.size = heads.size do
    throw <| .posCount heads.size pos.size

/-- Validate one half-open flattened range without normalizing caller coordinates. -/
private def checkRange (size start stop : Nat) : Except Error Unit := do
  unless start ≤ stop && stop ≤ size do
    throw <| .invalidRange start stop size

/-- Check local bounds, self loops, and the unique-root condition without a head slice. -/
private def checkRangeHeads (heads : Array Nat) (start stop : Nat) : Except TreeError Unit := do
  let width := stop - start
  if width = 0 then
    return ()
  let mut root : Option Nat := none
  for index in [start:stop] do
    let dependent := index - start + 1
    let head := heads[index]!
    if width < head then
      throw <| .headOutOfRange dependent head width
    if head = dependent then
      throw <| .selfHead dependent
    if head = 0 then
      match root with
      | none => root := some dependent
      | some first => throw <| .multipleRoots first dependent
  if root.isNone then
    throw .noRoot

/-- Check range-local acyclicity with dense local node identifiers and no extracted array. -/
private def checkRangeAcyclic (heads : Array Nat) (start stop : Nat) : Except TreeError Unit := do
  let width := stop - start
  let mut sets := UnionFind.empty (width + 1)
  for index in [start:stop] do
    let dependent := index - start + 1
    let head := heads[index]!
    match sets.connected dependent head with
    | none => throw <| .cycle dependent head
    | some (true, _) => throw <| .cycle dependent head
    | some (false, compressed) =>
      match compressed.union dependent head with
      | some joined => sets := joined
      | none => throw <| .cycle dependent head

/-- Validate one sentence-local tree stored inside flattened full-document columns. -/
private def checkRangeTree (heads : Array Nat) (start stop : Nat) : Except TreeError Unit := do
  checkRangeHeads heads start stop
  checkRangeAcyclic heads start stop

/-- Check the structural boundary needed for safe enhanced relation composition. -/
@[inline] private def relationValid (relation : String) : Bool :=
  !relation.isEmpty && relation != "_" &&
    !relation.startsWith ":" && !relation.endsWith ":" &&
    !relation.contains "::" &&
    relation.all fun character ↦ !character.isWhitespace && character != '|'

/-- Validate basic relation strings before interpreting roots or enhancement families. -/
private def checkRelations (relations : Array String) (start stop : Nat) : Except Error Unit := do
  for index in [start:stop] do
    let dependent := index - start + 1
    let relation := relations[index]!
    unless relationValid relation do
      throw <| .invalidRelation dependent relation

/-- Require root-headed words to carry exactly `root`, and only those words. -/
private def checkRootRelations (heads : Array Nat) (relations : Array String)
    (start stop : Nat) : Except Error Unit := do
  for index in [start:stop] do
    let dependent := index - start + 1
    let head := heads[index]!
    let relation := relations[index]!
    if head = 0 then
      unless relation == "root" do
        throw <| .rootRelationMismatch dependent head relation
    else if relation == "root" then
      throw <| .rootRelationMismatch dependent head relation

/-- Flat direct-child CSR with increasing sentence-local dependents in every parent row. -/
private structure ChildIndex where
  /-- One boundary before and after every artificial-root-or-word parent row. -/
  offsets : Array Nat
  /-- All direct dependents in parent-row order. -/
  dependents : Array Nat

/-- Build direct-child CSR with counting, prefix-sum, and fill passes. -/
private def childIndex (heads : Array Nat) (start stop : Nat) : ChildIndex := Id.run do
  let width := stop - start
  let mut counts := Array.replicate (width + 1) 0
  for index in [start:stop] do
    let head := heads[index]!
    counts := counts.set! head (counts[head]! + 1)
  let mut offsets := Array.emptyWithCapacity (width + 2)
  let mut total := 0
  offsets := offsets.push 0
  for parent in [0:width + 1] do
    total := total + counts[parent]!
    offsets := offsets.push total
  let mut cursors := offsets.extract 0 (width + 1)
  let mut dependents := Array.replicate width 0
  for index in [start:stop] do
    let dependent := index - start + 1
    let head := heads[index]!
    let slot := cursors[head]!
    dependents := dependents.set! slot dependent
    cursors := cursors.set! head (slot + 1)
  return ⟨offsets, dependents⟩

/-- First flat child position for one artificial-root-or-word parent. -/
@[inline] private def childStart (children : ChildIndex) (parent : Nat) : Nat :=
  children.offsets.getD parent 0

/-- Exclusive flat child position for one artificial-root-or-word parent. -/
@[inline] private def childStop (children : ChildIndex) (parent : Nat) : Nat :=
  children.offsets.getD (parent + 1) children.dependents.size

/-- Read one local dependent's relation from a flattened aligned column. -/
@[inline] private def relationAt (relations : Array String) (start dependent : Nat) : String :=
  relations[globalIndex start dependent]!

/-- Select the leftmost direct child whose relation belongs to either requested family. -/
private def leftmostMarker? (relations : Array String) (start : Nat)
    (children : ChildIndex) (dependent : Nat) (first second : String) : Option Nat := Id.run do
  for edge in [childStart children dependent:childStop children dependent] do
    let child := children.dependents[edge]!
    let relation := relationAt relations start child
    if relationIs relation first || (!second.isEmpty && relationIs relation second) then
      return some child
  return none

/-- Select the nearest preceding direct `cc`, falling back to the leftmost direct `cc`. -/
private def conjunctionMarker? (relations : Array String) (start : Nat)
    (children : ChildIndex) (dependent : Nat) : Option Nat := Id.run do
  let mut first : Option Nat := none
  let mut preceding : Option Nat := none
  for edge in [childStart children dependent:childStop children dependent] do
    let child := children.dependents[edge]!
    if relationIs (relationAt relations start child) "cc" then
      if first.isNone then
        first := some child
      if child < dependent then
        preceding := some child
  return preceding.orElse fun _ ↦ first

/-- Exact normalized UTF-8 size of a usable marker component, without allocating the result. -/
private def normalizedByteSize? (values : Array String) (start localIndex : Nat) : Option Nat :=
  let value := values[globalIndex start localIndex]!
  if value.isEmpty || value == "_" ||
      value.any fun character ↦
        character.isWhitespace || character == ':' || character == '|' then
    none
  else
    some <| value.foldl (fun total character ↦ total + character.toLower.utf8Size) 0

/-- A lexicalized-label plan that contains no materialized derived string. -/
private structure LexicalPlan where
  /-- Direct marker selected for this dependent. -/
  marker : Nat
  /-- Number of direct `fixed` members; positive means surface forms must be used. -/
  fixedCount : Nat
  /-- Exact UTF-8 bytes in the final relation label, including separators. -/
  labelBytes : Nat

/-- Plan one marker label and validate every selected component without joining strings. -/
private def markerPlan? (relations forms lemmas : Array String) (start : Nat)
    (children : ChildIndex) (dependent marker : Nat) : Option LexicalPlan := Id.run do
  let mut fixedCount := 0
  for edge in [childStart children marker:childStop children marker] do
    let child := children.dependents[edge]!
    if relationIs (relationAt relations start child) "fixed" then
      fixedCount := fixedCount + 1
  let mut nameBytes := fixedCount
  if fixedCount = 0 then
    let some bytes := normalizedByteSize? lemmas start marker
      | return none
    nameBytes := bytes
  else
    let some markerBytes := normalizedByteSize? forms start marker
      | return none
    nameBytes := nameBytes + markerBytes
    for edge in [childStart children marker:childStop children marker] do
      let child := children.dependents[edge]!
      if relationIs (relationAt relations start child) "fixed" then
        let some bytes := normalizedByteSize? forms start child
          | return none
        nameBytes := nameBytes + bytes
  let relationBytes := (relationAt relations start dependent).utf8ByteSize
  return some ⟨marker, fixedCount, relationBytes + 1 + nameBytes⟩

/-- Select and plan the direct marker for one basic relation. -/
private def lexicalPlan? (config : Config) (relations forms lemmas : Array String)
    (start : Nat) (children : ChildIndex) (dependent : Nat) : Option LexicalPlan := do
  let relation := relationAt relations start dependent
  let marker ←
    if config.lexicalizeNominals &&
        (relationIs relation "nmod" || relationIs relation "obl") then
      leftmostMarker? relations start children dependent "case" ""
    else if config.lexicalizeClauses &&
        (relationIs relation "acl" || relationIs relation "advcl") then
      leftmostMarker? relations start children dependent "mark" "case"
    else if config.lexicalizeConjunctions && relationIs relation "conj" then
      conjunctionMarker? relations start children dependent
    else
      none
  markerPlan? relations forms lemmas start children dependent marker

/-- Precompute at most one deterministic string-free lexicalization plan per word node. -/
private def lexicalPlans (config : Config) (relations forms lemmas : Array String)
    (start width : Nat) (children : ChildIndex) : Array (Option LexicalPlan) :=
  Array.ofFn (n := width) fun index ↦
    lexicalPlan? config relations forms lemmas start children (index.val + 1)

/-- Whether one conjunct receives its governor's incoming non-structural relation. -/
private def propagatesAt (config : Config) (heads : Array Nat) (relations : Array String)
    (start dependent : Nat) : Bool :=
  if !config.propagateIncomingConj ||
      !relationIs (relationAt relations start dependent) "conj" then
    false
  else
    let governor := heads[globalIndex start dependent]!
    governor != 0 && !propagationExcluded (relationAt relations start governor)

/-- Count lexicalized and propagated candidates after O(n) planning. -/
private def plannedCounts (config : Config) (heads : Array Nat) (relations : Array String)
    (start width : Nat) (plans : Array (Option LexicalPlan)) : Counts := Id.run do
  let mut lexicalizedCount := 0
  let mut propagatedCount := 0
  for index in [0:width] do
    let dependent := index + 1
    if (plans.getD index none).isSome then
      lexicalizedCount := lexicalizedCount + 1
    if propagatesAt config heads relations start dependent then
      propagatedCount := propagatedCount + 1
  return ⟨width, lexicalizedCount, propagatedCount⟩

/-- Exact aggregate UTF-8 bytes that all planned lexicalized labels will materialize. -/
private def plannedLexicalBytes (plans : Array (Option LexicalPlan)) : Nat :=
  plans.foldl (init := 0) fun total plan ↦
    total + (plan.map fun value ↦ value.labelBytes).getD 0

/-- Append one normalized marker part to a uniquely owned, pre-sized UTF-8 buffer. -/
@[inline] private def appendNormalizedPart (output : ByteArray) (separate : Bool)
    (value : String) : ByteArray :=
  let output := if separate then output.push 95 else output
  output.append value.toLower.toUTF8

/-- Materialize one prevalidated lexicalized relation in one linear UTF-8 buffer pass. -/
private def materializeLabel (relations forms lemmas : Array String) (start dependent : Nat)
    (children : ChildIndex) (plan : LexicalPlan) : String := Id.run do
  let relation := relationAt relations start dependent
  let mut output := ByteArray.emptyWithCapacity plan.labelBytes
  output := output.append relation.toUTF8
  output := output.push 58
  if plan.fixedCount = 0 then
    output := appendNormalizedPart output false lemmas[globalIndex start plan.marker]!
  else
    let mut inserted := false
    let mut wrotePart := false
    for edge in [childStart children plan.marker:childStop children plan.marker] do
      let child := children.dependents[edge]!
      if relationIs (relationAt relations start child) "fixed" then
        if !inserted && plan.marker < child then
          output := appendNormalizedPart output wrotePart forms[globalIndex start plan.marker]!
          wrotePart := true
          inserted := true
        output := appendNormalizedPart output wrotePart forms[globalIndex start child]!
        wrotePart := true
    unless inserted do
      output := appendNormalizedPart output wrotePart forms[globalIndex start plan.marker]!
  return String.fromUTF8! output

/-- Materialize every planned relation only after all exact public budgets have succeeded. -/
private def lexicalizedLabels (relations forms lemmas : Array String) (start width : Nat)
    (children : ChildIndex) (plans : Array (Option LexicalPlan)) : Array (Option String) :=
  Array.ofFn (n := width) fun index ↦
    (plans.getD index.val none).map fun plan ↦
      materializeLabel relations forms lemmas start (index.val + 1) children plan

/-- Map a sentence-local basic head coordinate to a graph node. -/
@[inline] private def graphHead (head : Nat) : NodeId :=
  if head = 0 then .root else .word head

/-- Compare canonical incoming keys; provenance intentionally does not affect graph order. -/
private def arcPrecedes (left right : Arc String) : Bool :=
  match left.head.compare right.head with
  | .lt => true
  | .gt => false
  | .eq => compare left.relation right.relation == .lt

/-- Build one canonical incoming row from its basic, lexicalized, and propagated arcs. -/
private def buildRow (config : Config) (heads : Array Nat) (relations : Array String)
    (start dependent : Nat) (lexicalized : Array (Option String)) : Row String := Id.run do
  let global := globalIndex start dependent
  let basicHead := heads[global]!
  let basicRelation := relations[global]!
  let mut incoming : Array (Arc String) :=
    #[⟨graphHead basicHead, basicRelation, .basic⟩]
  match lexicalized.getD (dependent - 1) none with
  | some relation =>
      incoming := incoming.push ⟨graphHead basicHead, relation, .enhanced⟩
  | none => pure ()
  if propagatesAt config heads relations start dependent then
    let governor := basicHead
    let governorGlobal := globalIndex start governor
    let propagatedHead := heads[governorGlobal]!
    let originalRelation := relations[governorGlobal]!
    let propagatedRelation :=
      (lexicalized.getD (governor - 1) none).getD originalRelation
    incoming := incoming.push
      ⟨graphHead propagatedHead, propagatedRelation, .enhanced⟩
  return ⟨.word dependent, incoming.mergeSort arcPrecedes⟩

/-- Emit every sentence-local word row after exact output limits have succeeded. -/
private def buildRows (config : Config) (heads : Array Nat) (relations : Array String)
    (start width : Nat) (lexicalized : Array (Option String)) : Array (Row String) :=
  Array.ofFn (n := width) fun index ↦
    buildRow config heads relations start (index.val + 1) lexicalized

/-- Seal canonical rows and prove their predicted word and edge counts at runtime. -/
private def compileResult (rows : Array (Row String)) (counts : Counts) : Except Error Result := do
  let graphConfig : GraphConfig :=
    { maxEntries := Graph.requiredEntries counts.basic counts.total }
  let graph ←
    match Graph.ofRowsWith graphConfig rows with
    | .ok graph => pure graph
    | .error cause => throw <| .graph cause
  if nodes : graph.nodeCount = counts.basic then
    if edges : graph.edgeCount = counts.total then
      return .mk graph counts nodes edges
    else
      throw <| .inconsistentGraphCounts counts.basic graph.nodeCount counts.total
        graph.edgeCount
  else
    throw <| .inconsistentGraphCounts counts.basic graph.nodeCount counts.total
      graph.edgeCount

/-- Run the trusted range kernel after column, range, and tree validation. -/
private def enhanceCheckedRange (config : Config) (heads : Array Nat)
    (relations forms lemmas : Array String) (start stop : Nat) : Except Error Result := do
  let width := stop - start
  checkRelations relations start stop
  checkRootRelations heads relations start stop
  if config.maxEdges < width then
    throw <| .edgeBudget width config.maxEdges
  let children := childIndex heads start stop
  let plans := lexicalPlans config relations forms lemmas start width children
  let counts := plannedCounts config heads relations start width plans
  if config.maxCandidates < counts.candidates then
    throw <| .candidateBudget counts.candidates config.maxCandidates
  if config.maxEdges < counts.total then
    throw <| .edgeBudget counts.total config.maxEdges
  let lexicalBytes := plannedLexicalBytes plans
  if config.maxLexicalBytes < lexicalBytes then
    throw <| .lexicalBudget lexicalBytes config.maxLexicalBytes
  let lexicalized := lexicalizedLabels relations forms lemmas start width children plans
  compileResult (buildRows config heads relations start width lexicalized) counts

/--
Enhance one checked tree while validating its aligned lexical columns.

The checked tree proof avoids repeating head validation. Surface forms are used for fixed marker
expressions; lemmas remain the normal source for single-word markers. POS is retained so future
strictly bounded English rules can use it without changing the public sentence contract.
-/
def enhanceTreeWith? (config : Config) (tree : Tree String)
    (forms lemmas pos : Array String) : Except Error Result := do
  checkColumns tree.heads tree.relations forms lemmas pos
  enhanceCheckedRange config tree.heads tree.relations forms lemmas 0 tree.heads.size

/-- Enhance one checked tree with the production configuration. -/
@[inline] def enhanceTree? (tree : Tree String) (forms lemmas pos : Array String) :
    Except Error Result :=
  enhanceTreeWith? .default tree forms lemmas pos

/--
Validate and enhance one sentence range directly over aligned flattened document columns.

Heads retain sentence-local CoNLL-U coordinates inside the selected range. The output graph uses
sentence-local `.word 1 .. .word (stop - start)` nodes. No input column or sentence slice is
allocated.
-/
def enhanceRangeWith? (config : Config) (heads : Array Nat) (relations forms lemmas pos :
    Array String) (start stop : Nat) : Except Error Result := do
  checkColumns heads relations forms lemmas pos
  checkRange heads.size start stop
  match checkRangeTree heads start stop with
  | .error cause => throw <| .invalidTree cause
  | .ok () => enhanceCheckedRange config heads relations forms lemmas start stop

/-- Enhance one flattened sentence range with the production configuration. -/
@[inline] def enhanceRange? (heads : Array Nat) (relations forms lemmas pos : Array String)
    (start stop : Nat) : Except Error Result :=
  enhanceRangeWith? .default heads relations forms lemmas pos start stop

/-- Validate and enhance complete aligned arrays under an explicit configuration. -/
@[inline] def enhanceArraysWith? (config : Config) (heads : Array Nat)
    (relations forms lemmas pos : Array String) : Except Error Result :=
  enhanceRangeWith? config heads relations forms lemmas pos 0 heads.size

/-- Validate and enhance complete aligned arrays with the production configuration. -/
@[inline] def enhanceArrays? (heads : Array Nat) (relations forms lemmas pos : Array String) :
    Except Error Result :=
  enhanceArraysWith? .default heads relations forms lemmas pos

end Nlp.Dependency.EnglishEnhanced
