import Std.Data.HashMap
import Nlp.Core.Data.FloatArrayExt
import Nlp.Core.Score.Cost
import Nlp.Dependency.Eisner

/-!
# Compiled labeled dependency-arc scores

This module moves label selection out of projective dependency parsing's cubic loop. A caller
supplies one cost for each `(head, dependent, relation)` candidate. Compilation retains the
lowest-cost relation for every directed arc, with the lower relation ordinal winning exact ties.

Heads and dependents use CoNLL-U coordinates: dependents are `1 .. n`, head `0` is the artificial
root, and nonzero heads name tokens. Root arcs consider only the configured root relation;
token-to-token arcs exclude it. Positive infinity forbids a candidate. Every other accepted cost
is finite, nonnegative, and uses canonical positive zero.
-/

namespace Nlp.Dependency

/-- Resource limits for compiling one sentence's labeled arc scores. -/
structure ArcScoreConfig where
  /-- Maximum number of real tokens. -/
  maxTokens : Nat := 4096
  /-- Maximum number of relation names. -/
  maxRelations : Nat := 4096
  /-- Maximum number of compiled directed-arc slots. -/
  maxArcEntries : Nat := 16_777_216
  /-- Maximum number of legal labeled candidates visited through a scorer. -/
  maxScoreVisits : Nat := 67_108_864
  /-- Maximum number of entries accepted by the dense input adapter. -/
  maxDenseScores : Nat := 67_108_864
  deriving Repr, DecidableEq, Inhabited

namespace ArcScoreConfig

/-- Production defaults for sentence-local score compilation. -/
def default : ArcScoreConfig := {}

end ArcScoreConfig

/-- Why labeled sentence scores could not be compiled. -/
inductive ArcScoreError where
  | tokenCapacity (count : Nat)
  | tokenBudget (required limit : Nat)
  | relationCapacity (count : Nat)
  | relationBudget (required limit : Nat)
  | zeroRelations
  | invalidRootRelation (root relations : Nat)
  | emptyRelationName (index : Nat)
  | duplicateRelationName (first duplicate : Nat) (name : String)
  | arcEntryBudget (required limit : Nat)
  | scoreVisitBudget (required limit : Nat)
  | denseScoreBudget (required limit : Nat)
  | denseDimension (expected found : Nat)
  | invalidCost (head dependent relation : Nat) (value : Float) (bits : UInt64)
  deriving Repr

/-- One chosen relation and its canonical finite cost. -/
structure ArcChoice where
  /-- Min-plus cost of the selected arc label. -/
  cost : Float
  /-- Exact ordinal in the caller's relation-name array. -/
  relation : UInt32
  deriving Repr, DecidableEq, Inhabited

/--
Sentence-specific directed arcs after label alternatives have been collapsed.

The flat arc index is `head * n + (dependent - 1)`. Unavailable and self arcs store positive
infinity; callers observe them as `none` through `choice?`.
-/
structure ArcScores where
  private mk ::
  /-- Number of real tokens represented by the table. -/
  n : Nat
  /-- Ordered relation names; ordinals are preserved exactly. -/
  relationNames : Array String
  /-- Relation reserved for the artificial-root arc. -/
  rootRelation : UInt32
  /-- One unboxed best cost for every `(head, dependent)` slot. -/
  costs : FloatArray
  /-- Parallel exact source-relation ordinals. -/
  relations : Array UInt32

namespace ArcScores

/-- A pure sentence scorer in 1-based dependency coordinates. -/
abbrev Scorer := Nat → Nat → Nat → Float

/-- Number of directed-arc slots in a compiled table, including root and self slots. -/
@[inline] def entryCount (n : Nat) : Nat := (n + 1) * n

/-- Number of legal labeled candidates visited during scorer compilation. -/
@[inline] def scoreVisitCount (n relations : Nat) : Nat :=
  n + n * (n - 1) * (relations - 1)

/-- Number of values in the dense `(head, dependent, relation)` representation. -/
@[inline] def denseEntryCount (n relations : Nat) : Nat := entryCount n * relations

/-- Flat compiled index for a head and 1-based dependent. -/
@[inline] def index (n head dependent : Nat) : Nat :=
  head * n + (dependent - 1)

/-- Flat dense-source index for a labeled head-dependent candidate. -/
@[inline] def denseIndex (n relations head dependent relation : Nat) : Nat :=
  index n head dependent * relations + relation

/-- The IEEE-754 representation of canonical positive infinity. -/
private def positiveInfinityBits : UInt64 := inf.toBits

/-- The IEEE-754 representation of noncanonical negative zero. -/
private def negativeZeroBits : UInt64 := 0x8000000000000000

/-- Accepted costs are nonnegative finite values or canonical positive infinity. -/
@[inline] def isCanonicalCost (value : Float) : Bool :=
  (value.isFinite || value.toBits == positiveInfinityBits) &&
    decide (0.0 <= value) && value.toBits != negativeZeroBits

/-- Report one invalid numeric candidate without erasing its source coordinates. -/
@[inline] private def validateCost (head dependent relation : Nat) (value : Float) :
    Except ArcScoreError Unit :=
  if isCanonicalCost value then
    .ok ()
  else
    .error (.invalidCost head dependent relation value value.toBits)

/-- Validate names once while retaining both positions of the first duplicate. -/
private def validateRelationNames (names : Array String) : Except ArcScoreError Unit := do
  let mut seen : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity names.size
  for index in [0:names.size] do
    let name := names[index]!
    if name.isEmpty then
      throw <| .emptyRelationName index
    match seen.get? name with
    | some first => throw <| .duplicateRelationName first index name
    | none => seen := seen.insert name index

/-- Validate capacities and exact allocation work before invoking a scorer. -/
private def validateShape (config : ArcScoreConfig) (n relations rootRelation : Nat) :
    Except ArcScoreError Unit := do
  if UInt32.size ≤ n then
    throw <| .tokenCapacity n
  if config.maxTokens < n then
    throw <| .tokenBudget n config.maxTokens
  if relations = 0 then
    throw .zeroRelations
  if UInt32.size < relations then
    throw <| .relationCapacity relations
  if config.maxRelations < relations then
    throw <| .relationBudget relations config.maxRelations
  unless rootRelation < relations do
    throw <| .invalidRootRelation rootRelation relations
  let entries := entryCount n
  if config.maxArcEntries < entries then
    throw <| .arcEntryBudget entries config.maxArcEntries
  let visits := scoreVisitCount n relations
  if config.maxScoreVisits < visits then
    throw <| .scoreVisitBudget visits config.maxScoreVisits

/--
Compile a labeled scorer, selecting labels before projective inference.

Scorer calls are deterministic: root candidates appear in dependent order, followed by
token-to-token arcs in dependent, head, relation order. Illegal self arcs and semantically
irrelevant root-relation combinations are never evaluated.
-/
def compileScorerWith (config : ArcScoreConfig) (n : Nat)
    (relationNames : Array String) (rootRelation : Nat) (score : Scorer) :
    Except ArcScoreError ArcScores := do
  validateShape config n relationNames.size rootRelation
  validateRelationNames relationNames
  let entries := entryCount n
  let mut costs := FloatArray.replicate entries inf
  let mut relations := Array.replicate entries (UInt32.ofNat rootRelation)
  for dependent in [1:n + 1] do
    let rootCost := score 0 dependent rootRelation
    validateCost 0 dependent rootRelation rootCost
    let rootIndex := index n 0 dependent
    costs := costs.set! rootIndex rootCost
    for head in [1:n + 1] do
      unless head == dependent do
        let mut best := inf
        let mut bestRelation := UInt32.ofNat rootRelation
        for relation in [0:relationNames.size] do
          unless relation == rootRelation do
            let candidate := score head dependent relation
            validateCost head dependent relation candidate
            if candidate < best then
              best := candidate
              bestRelation := UInt32.ofNat relation
        let arcIndex := index n head dependent
        costs := costs.set! arcIndex best
        relations := relations.set! arcIndex bestRelation
  return .mk n relationNames (UInt32.ofNat rootRelation) costs relations

/-- Compile a labeled scorer under production resource limits. -/
@[inline] def compileScorer (n : Nat) (relationNames : Array String)
    (rootRelation : Nat) (score : Scorer) : Except ArcScoreError ArcScores :=
  compileScorerWith .default n relationNames rootRelation score

/-- Decode the coordinates of one row-major dense source entry. -/
private def denseCoordinates (n relations source : Nat) : Nat × Nat × Nat :=
  let arc := source / relations
  (arc / n, arc % n + 1, source % relations)

/--
Compile an exact row-major dense score tensor.

Dense storage contains every head, dependent, and relation combination, including combinations
ignored by dependency semantics. All entries are validated so malformed hidden data is rejected.
-/
def compileDenseWith (config : ArcScoreConfig) (n : Nat)
    (relationNames : Array String) (rootRelation : Nat) (values : Array Float) :
    Except ArcScoreError ArcScores := do
  let expected := denseEntryCount n relationNames.size
  if values.size != expected then
    throw <| .denseDimension expected values.size
  if config.maxDenseScores < expected then
    throw <| .denseScoreBudget expected config.maxDenseScores
  validateShape config n relationNames.size rootRelation
  validateRelationNames relationNames
  for source in [0:values.size] do
    let (head, dependent, relation) := denseCoordinates n relationNames.size source
    validateCost head dependent relation values[source]!
  compileScorerWith config n relationNames rootRelation fun head dependent relation =>
    values.getD (denseIndex n relationNames.size head dependent relation) inf

/-- Compile a dense score tensor under production resource limits. -/
@[inline] def compileDense (n : Nat) (relationNames : Array String)
    (rootRelation : Nat) (values : Array Float) : Except ArcScoreError ArcScores :=
  compileDenseWith .default n relationNames rootRelation values

/-- Read a compiled cost, returning infinity outside legal dependency coordinates. -/
@[inline] def costAt (scores : ArcScores) (head dependent : Nat) : Float :=
  if head ≤ scores.n && 1 ≤ dependent && dependent ≤ scores.n && head != dependent then
    scores.costs.getD (index scores.n head dependent) inf
  else
    inf

/-- Read the chosen relation exactly when a legal directed arc has finite cost. -/
@[inline] def choice? (scores : ArcScores) (head dependent : Nat) : Option ArcChoice :=
  let cost := scores.costAt head dependent
  if cost.isFinite then
    let relation := scores.relations.getD (index scores.n head dependent)
      scores.rootRelation
    some ⟨cost, relation⟩
  else
    none

/-- Resolve one compiled relation ordinal to its exact caller-supplied name. -/
@[inline] def relationName? (scores : ArcScores) (relation : UInt32) : Option String :=
  scores.relationNames[relation.toNat]?

/-- Project compiled one-based arc costs into the generic zero-based Eisner recurrence. -/
def toArcWeights (scores : ArcScores) : Eisner.ArcWeights Cost where
  n := scores.n
  rootWeight := fun dependent => ⟨scores.costAt 0 (dependent + 1)⟩
  tokenWeight := fun head dependent => ⟨scores.costAt (head + 1) (dependent + 1)⟩

/-- Every successfully observed choice has a finite cost. -/
theorem isFinite_of_choice?_eq_some (scores : ArcScores) (head dependent : Nat)
    (choice : ArcChoice) (found : scores.choice? head dependent = some choice) :
    choice.cost.isFinite = true := by
  simp only [choice?] at found
  split at found
  · rename_i finite
    cases found
    exact finite
  · contradiction

end ArcScores

end Nlp.Dependency
