import Std.Data.HashMap
import Nlp.Core.Data.DependencyGraph
import Nlp.IO.ConlluReader

/-!
# Typed CoNLL-U enhanced dependencies

The lossless reader deliberately retains `DEPS` as text. This module gives that column a checked
semantic layer without claiming to implement the complete, language-sensitive Unicode grammar
for enhanced relation labels. It enforces the structural field grammar: a nonempty relation is a
colon-separated sequence of nonempty, whitespace-free sections, and it contains no CoNLL-U field
or dependency-list delimiter.

`_` means that enhanced dependencies are unspecified. It is distinct from an explicitly
present empty dependency list, which the format does not admit. Heads are root `0`, ordinary
word IDs, or empty-node IDs. Multiword-token ranges and implementation-only copy nodes are
rejected.
-/

namespace Nlp.IO

open Nlp.Dependency

/-- One typed `HEAD:DEPREL` item from a CoNLL-U `DEPS` field. -/
structure EnhancedArc where
  /-- Root, word, or empty-node head. -/
  head : NodeId
  /-- Structurally checked enhanced relation label. -/
  relation : String
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A deterministic failure while decoding or validating one `DEPS` field. -/
inductive DepsError where
  | emptyPresentField
  | emptyItem (index : Nat)
  | missingSeparator (index : Nat) (item : String)
  | emptyHead (index : Nat)
  | malformedHead (index : Nat) (head : String)
  | rangeHead (index first last : Nat)
  | copyHead (index : Nat) (head : String)
  | invalidHead (index : Nat) (head : NodeId)
  | emptyRelation (index : Nat) (head : NodeId)
  | invalidRelation (index : Nat) (relation : String)
  | noncanonicalHeadOrder (index : Nat) (previous current : NodeId)
  | duplicateArc (first duplicate : Nat) (head : NodeId) (relation : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Render a graph node in the head position of a `DEPS` item.

The `.copy` rendering is intentionally outside CoNLL-U syntax. Such values fail `EnhancedArc.WF`
and therefore have no round-trip guarantee.
-/
def renderDepsHead : NodeId → String
  | .root => "0"
  | .word index => toString index
  | .empty anchor copy => s!"{anchor}.{copy}"
  | .copy index copy => s!"{index}.{copy}.copy"

/-- The structural relation-label boundary implemented here.

This accepts Unicode and language-specific relation sections. It does not pretend to decide the
complete UD language-specific label grammar.
-/
def enhancedRelationValid (relation : String) : Bool :=
  !relation.isEmpty && relation != "_" &&
    (relation.splitOn ":").all (!String.isEmpty ·) &&
    relation.toList.all fun character ↦
      !character.isWhitespace && character != '|' && character != '\t' &&
        character != '\n' && character != '\r'

/-- Executable canonicality conditions for one enhanced arc. -/
def EnhancedArc.wf (arc : EnhancedArc) : Bool :=
  arc.head.valid &&
    (match arc.head with
    | .root | .word _ | .empty _ _ => true
    | .copy _ _ => false) &&
    enhancedRelationValid arc.relation

/-- Canonicality of one enhanced arc as a proposition. -/
def EnhancedArc.WF (arc : EnhancedArc) : Prop := arc.wf = true

instance instDecidableEnhancedArcWF (arc : EnhancedArc) : Decidable arc.WF := by
  unfold EnhancedArc.WF
  infer_instance

@[inline] private def headAfter (previous current : NodeId) : Bool :=
  NodeId.compare previous current != .gt

/-- Validate a semantic optional `DEPS` value without reparsing text. -/
def checkDeps : Option (Array EnhancedArc) → Except DepsError Unit
  | none => .ok ()
  | some arcs => do
    if arcs.isEmpty then
      throw .emptyPresentField
    let mut previous : Option NodeId := none
    let mut firstIndex : Std.HashMap (NodeId × String) Nat := {}
    for index in [0:arcs.size] do
      let arc := arcs[index]!
      unless arc.head.valid do
        throw <| .invalidHead index arc.head
      match arc.head with
      | .copy _ _ => throw <| .copyHead index (renderDepsHead arc.head)
      | .root | .word _ | .empty _ _ => pure ()
      unless enhancedRelationValid arc.relation do
        if arc.relation.isEmpty then
          throw <| .emptyRelation index arc.head
        else
          throw <| .invalidRelation index arc.relation
      match previous with
      | some prior =>
        unless headAfter prior arc.head do
          throw <| .noncanonicalHeadOrder index prior arc.head
      | none => pure ()
      let key := (arc.head, arc.relation)
      match firstIndex[key]? with
      | some first => throw <| .duplicateArc first index arc.head arc.relation
      | none => firstIndex := firstIndex.insert key index
      previous := some arc.head

/-- Canonical semantic `DEPS` values are exactly those accepted by `checkDeps`. -/
def DepsWF (deps : Option (Array EnhancedArc)) : Prop := checkDeps deps = .ok ()

instance instDecidableDepsWF (deps : Option (Array EnhancedArc)) : Decidable (DepsWF deps) :=
  match checked : checkDeps deps with
  | .ok () => isTrue (by simpa [DepsWF] using checked)
  | .error cause => isFalse (by simp [DepsWF, checked])

/-- The semantic well-formedness predicate is exactly acceptance by the executable checker. -/
theorem checkDeps_eq_ok_iff (deps : Option (Array EnhancedArc)) :
    checkDeps deps = .ok () ↔ DepsWF deps :=
  Iff.rfl

private def splitEnhancedItem? (item : String) : Option (String × String) :=
  match item.splitOn ":" with
  | [] | [_] => none
  | head :: relation => some (head, String.intercalate ":" relation)

private def looksLikeCopyId (raw : String) : Bool :=
  2 < (raw.splitOn ".").length

private def parseDepsHead (index : Nat) (raw : String) : Except DepsError NodeId := do
  if raw.isEmpty then
    throw <| .emptyHead index
  if raw = "0" then
    return .root
  if looksLikeCopyId raw then
    throw <| .copyHead index raw
  match ConlluId.parse raw with
  | some (.word word) => return .word word
  | some (.empty anchor copy) => return .empty anchor copy
  | some (.range first last) => throw <| .rangeHead index first last
  | none => throw <| .malformedHead index raw

private def parseEnhancedItem (index : Nat) (item : String) : Except DepsError EnhancedArc := do
  if item.isEmpty then
    throw <| .emptyItem index
  let (headRaw, relation) ←
    match splitEnhancedItem? item with
    | some parts => pure parts
    | none => throw <| .missingSeparator index item
  let head ← parseDepsHead index headRaw
  if relation.isEmpty then
    throw <| .emptyRelation index head
  unless enhancedRelationValid relation do
    throw <| .invalidRelation index relation
  return { head, relation }

private def parseDepsCandidate
    (field : String) : Except DepsError (Option (Array EnhancedArc)) := do
  if field = "_" then
    return none
  if field.isEmpty then
    throw .emptyPresentField
  let items := field.splitOn "|"
  let mut arcs := Array.emptyWithCapacity items.length
  let mut index := 0
  for item in items do
    arcs := arcs.push (← parseEnhancedItem index item)
    index := index + 1
  return some arcs

/-- Parse an optional CoNLL-U `DEPS` field.

`_` returns `none`. Present fields must contain a nonempty `|`-separated list in nondecreasing
numeric head order. Exact `(head, relation)` duplicates are rejected; distinct labels at the same
head remain valid.
-/
def parseDeps (field : String) : Except DepsError (Option (Array EnhancedArc)) :=
  match parseDepsCandidate field with
  | .error cause => .error cause
  | .ok result =>
    match checkDeps result with
    | .error cause => .error cause
    | .ok () => .ok result

/-- Every successful parse produces a value accepted by the semantic checker. -/
theorem parseDeps_sound {field : String} {deps : Option (Array EnhancedArc)}
    (parsed : parseDeps field = .ok deps) : DepsWF deps := by
  cases candidate : parseDepsCandidate field with
  | error cause => simp [parseDeps, candidate] at parsed
  | ok result =>
      cases checked : checkDeps result with
      | error cause => simp [parseDeps, candidate, checked] at parsed
      | ok value =>
          cases value
          simp [parseDeps, candidate, checked] at parsed
          subst deps
          exact checked

/-- Render an optional typed `DEPS` value.

`none` renders as the reserved `_`. Invalid `some #[]` and copy-node values render
deterministically but are outside the checked round-trip contract.
-/
def renderDeps : Option (Array EnhancedArc) → String
  | none => "_"
  | some arcs =>
    String.intercalate "|" <| arcs.toList.map fun arc ↦
      renderDepsHead arc.head ++ ":" ++ arc.relation

/-! ## Lossless-sentence projection -/

/-- A typed failure while projecting lossless CoNLL-U rows into an enhanced graph. -/
inductive DependencyGraphError where
  | malformedId (row : Nat) (value : String)
  | nonsequentialWordId (row expected found : Nat)
  | invalidEmptyNodeAnchor (row : Nat) (expected : Option Nat) (found : Nat)
  | nonsequentialEmptyNodeId (row anchor expected found : Nat)
  | deps (row : Nat) (cause : DepsError)
  | mixedDepsPresence (presentRow missingRow : Nat)
  | emptyNodeDepsRequired (row : Nat) (id : NodeId)
  | emptyNodeHeadPresent (row : Nat) (value : String)
  | emptyNodeDeprelPresent (row : Nat) (value : String)
  | graph (cause : GraphError String)
  deriving Repr

@[inline] private def graphArcPrecedes (left right : Arc String) : Bool :=
  match NodeId.compare left.head right.head with
  | .lt => true
  | .gt => false
  | .eq => compare left.relation right.relation == .lt

private def graphIncoming (arcs : Array EnhancedArc) : Array (Arc String) :=
  (arcs.map fun arc ↦
    { head := arc.head, relation := arc.relation, origin := Origin.enhanced }).mergeSort
      graphArcPrecedes

/-- Project present `DEPS` columns into a checked directed graph.

Word and empty-node rows become graph nodes; multiword-token range rows are ignored. Every word
and empty-node row must agree on whether `DEPS` is present. Empty nodes must retain missing basic
`HEAD` and `DEPREL` fields. Word identifiers must be `1 .. n`; empty suffixes at root position zero
or the most recent word must start at `.1` and remain contiguous. Endpoint, duplicate-row, and
canonical CSR validation is delegated to `Graph.ofRows`.
-/
def ConlluSentence.toDependencyGraph (sentence : ConlluSentence) :
    Except DependencyGraphError (Option (Graph String)) := do
  let mut rows : Array (Row String) := #[]
  let mut firstPresent : Option Nat := none
  let mut firstMissing : Option Nat := none
  let mut nextWord := 1
  let mut emptyAnchor? : Option Nat := some 0
  let mut nextEmpty := 1
  for rowIndex in [0:sentence.rows.size] do
    let sourceRow := rowIndex + 1
    let row := sentence.rows[rowIndex]!
    let id ←
      match ConlluId.parse row.id with
      | some value => pure value
      | none => throw <| .malformedId sourceRow row.id
    match id with
    | .range _ _ =>
      emptyAnchor? := none
    | .word _ | .empty _ _ =>
      let dependent :=
        match id with
        | .word word => NodeId.word word
        | .empty anchor copy => NodeId.empty anchor copy
        | .range _ _ => NodeId.root
      match id with
      | .word word =>
        unless word = nextWord do
          throw <| .nonsequentialWordId sourceRow nextWord word
        nextWord := nextWord + 1
        emptyAnchor? := some word
        nextEmpty := 1
      | .empty anchor copy =>
        unless emptyAnchor? = some anchor do
          throw <| .invalidEmptyNodeAnchor sourceRow emptyAnchor? anchor
        unless copy = nextEmpty do
          throw <| .nonsequentialEmptyNodeId sourceRow anchor nextEmpty copy
        nextEmpty := nextEmpty + 1
        match row.head with
        | .present value _ => throw <| .emptyNodeHeadPresent sourceRow value
        | .missing => pure ()
        match row.deprel with
        | .present value _ => throw <| .emptyNodeDeprelPresent sourceRow value
        | .missing => pure ()
        match row.deps with
        | .missing => throw <| .emptyNodeDepsRequired sourceRow dependent
        | .present field _ =>
          if field.isEmpty || field = "_" then
            throw <| .emptyNodeDepsRequired sourceRow dependent
      | .range _ _ => pure ()
      match row.deps with
      | .missing =>
        if firstMissing.isNone then
          firstMissing := some sourceRow
        rows := rows.push { dependent, incoming := #[] }
      | .present field _ =>
        let parsed ←
          match parseDeps field with
          | .ok (some arcs) => pure arcs
          | .ok none =>
            if firstMissing.isNone then
              firstMissing := some sourceRow
            pure #[]
          | .error cause => throw <| .deps sourceRow cause
        if firstPresent.isNone && field != "_" then
          firstPresent := some sourceRow
        rows := rows.push { dependent, incoming := graphIncoming parsed }
  match firstPresent, firstMissing with
  | none, _ => return none
  | some present, some missing => throw <| .mixedDepsPresence present missing
  | some _, none =>
    match Graph.ofRows rows with
    | .ok graph => return some graph
    | .error cause => throw <| .graph cause

end Nlp.IO
