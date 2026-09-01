import Nlp.Core.Data.UnionFind

/-!
# Dependency-tree foundations

Dependency heads use the sentence-local CoNLL-U convention. Dependents are numbered `1 .. n`,
head `0` is the artificial root, and every nonzero head is another 1-based word position in the
same sentence. General tree validity is deliberately separate from projectivity: a valid
dependency tree may contain crossing arcs.
-/

namespace Nlp.Dependency

/-- A deterministic failure produced while checking one sentence's dependency heads. -/
inductive TreeError where
  /-- A head lies outside the artificial-root-plus-token range `0 .. n`. -/
  | headOutOfRange (dependent head tokenCount : Nat)
  /-- A word selects itself as its head. -/
  | selfHead (dependent : Nat)
  /-- A nonempty sentence has no word attached to the artificial root. -/
  | noRoot
  /-- Two words are attached directly to the artificial root. -/
  | multipleRoots (first second : Nat)
  /-- Adding this dependency closes a cycle in left-to-right dependent order. -/
  | cycle (dependent head : Nat)
  /-- A relation column does not have exactly one value per dependent. -/
  | relationCount (expected found : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A crossing witness returned in deterministic dependent-pair order. -/
inductive ProjectivityError where
  /-- Projectivity was requested for heads that do not form a dependency tree. -/
  | invalidTree (cause : TreeError)
  /-- Two arcs have strictly interleaving endpoints. -/
  | crossing (firstDependent firstHead secondDependent secondHead : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A failure while validating sentence-local trees in one flattened document. -/
inductive DocumentTreeError where
  /-- Sentence ends are empty, non-increasing, out of bounds, or do not cover all heads. -/
  | invalidSentenceEnds (heads : Nat) (ends : Array Nat)
  /-- One sentence failed after its local head slice was isolated. -/
  | sentence (index start stop : Nat) (cause : TreeError)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Check local head bounds, self loops, and the unique-root condition from left to right. -/
private def checkLocalHeads (heads : Array Nat) : Except TreeError Unit := do
  if heads.isEmpty then
    return ()
  let mut root : Option Nat := none
  for index in [0:heads.size] do
    let dependent := index + 1
    let head := heads[index]!
    if heads.size < head then
      throw <| .headOutOfRange dependent head heads.size
    if head = dependent then
      throw <| .selfHead dependent
    if head = 0 then
      match root with
      | none => root := some dependent
      | some first => throw <| .multipleRoots first dependent
  if root.isNone then
    throw .noRoot

/-- Check for an undirected cycle while adding directed parent edges in dependent order. -/
private def checkAcyclic (heads : Array Nat) : Except TreeError Unit := do
  let mut sets := UnionFind.empty (heads.size + 1)
  for index in [0:heads.size] do
    let dependent := index + 1
    let head := heads[index]!
    match sets.connected dependent head with
    | none => throw <| .cycle dependent head
    | some (true, _) => throw <| .cycle dependent head
    | some (false, compressed) =>
      match compressed.union dependent head with
      | some joined => sets := joined
      | none => throw <| .cycle dependent head

/--
Validate one sentence's 1-based heads.

The empty head array is the empty tree. A nonempty result has in-range non-self heads, exactly
one root dependent, and no cycle. Bounds, self loops, and roots are diagnosed left to right;
cycles are then diagnosed by the edge that first closes one in dependent order.
-/
def checkSentenceTree (heads : Array Nat) : Except TreeError Unit := do
  checkLocalHeads heads
  checkAcyclic heads

/-- Executable semantic well-formedness for one sentence's dependency-head column. -/
def SentenceTreeWF (heads : Array Nat) : Prop :=
  match checkSentenceTree heads with
  | .ok () => True
  | .error _ => False

instance (heads : Array Nat) : Decidable (SentenceTreeWF heads) :=
  match checked : checkSentenceTree heads with
  | .ok () => isTrue (by simp [SentenceTreeWF, checked])
  | .error cause => isFalse (by simp [SentenceTreeWF, checked])

/-- The tree checker succeeds exactly when its executable semantic predicate holds. -/
theorem checkSentenceTree_eq_ok_iff (heads : Array Nat) :
    checkSentenceTree heads = .ok () ↔ SentenceTreeWF heads := by
  cases checked : checkSentenceTree heads with
  | error cause => simp [SentenceTreeWF, checked]
  | ok value => cases value; simp [SentenceTreeWF, checked]

/--
Validate sentence-local heads stored consecutively in one flattened document.

`sentenceEnds` uses exclusive token offsets. Empty documents require no ends; nonempty documents
require nonempty, strictly increasing ends whose last value is exactly `heads.size`.
-/
def checkDocumentTrees (heads sentenceEnds : Array Nat) : Except DocumentTreeError Unit := do
  if heads.isEmpty then
    unless sentenceEnds.isEmpty do
      throw <| .invalidSentenceEnds heads.size sentenceEnds
    return ()
  if sentenceEnds.isEmpty then
    throw <| .invalidSentenceEnds heads.size sentenceEnds
  let mut start := 0
  for sentenceIndex in [0:sentenceEnds.size] do
    let stop := sentenceEnds[sentenceIndex]!
    unless start < stop && stop ≤ heads.size do
      throw <| .invalidSentenceEnds heads.size sentenceEnds
    match checkSentenceTree (heads.extract start stop) with
    | .ok () => pure ()
    | .error cause => throw <| .sentence sentenceIndex start stop cause
    start := stop
  unless start = heads.size do
    throw <| .invalidSentenceEnds heads.size sentenceEnds

/-- Executable semantic validity for flattened sentence-local dependency trees. -/
def DocumentTreeWF (heads sentenceEnds : Array Nat) : Prop :=
  match checkDocumentTrees heads sentenceEnds with
  | .ok () => True
  | .error _ => False

instance (heads sentenceEnds : Array Nat) : Decidable (DocumentTreeWF heads sentenceEnds) :=
  match checked : checkDocumentTrees heads sentenceEnds with
  | .ok () => isTrue (by simp [DocumentTreeWF, checked])
  | .error cause => isFalse (by simp [DocumentTreeWF, checked])

/-- The flattened checker succeeds exactly for its executable semantic predicate. -/
theorem checkDocumentTrees_eq_ok_iff (heads sentenceEnds : Array Nat) :
    checkDocumentTrees heads sentenceEnds = .ok () ↔ DocumentTreeWF heads sentenceEnds := by
  cases checked : checkDocumentTrees heads sentenceEnds with
  | error cause => simp [DocumentTreeWF, checked]
  | ok value => cases value; simp [DocumentTreeWF, checked]

/-- Whether two dependency arcs have strictly interleaving endpoint intervals. -/
@[inline] def arcsCross (firstHead firstDependent secondHead secondDependent : Nat) : Bool :=
  let firstLeft := min firstHead firstDependent
  let firstRight := max firstHead firstDependent
  let secondLeft := min secondHead secondDependent
  let secondRight := max secondHead secondDependent
  (firstLeft < secondLeft && secondLeft < firstRight && firstRight < secondRight) ||
    (secondLeft < firstLeft && firstLeft < secondRight && secondRight < firstRight)

/-- The first crossing pair in increasing first-dependent, then second-dependent order. -/
private def firstCrossing? (heads : Array Nat) :
    Option (Nat × Nat × Nat × Nat) := Id.run do
  for firstIndex in [0:heads.size] do
    let firstDependent := firstIndex + 1
    let firstHead := heads[firstIndex]!
    for secondIndex in [firstIndex + 1:heads.size] do
      let secondDependent := secondIndex + 1
      let secondHead := heads[secondIndex]!
      if arcsCross firstHead firstDependent secondHead secondDependent then
        return some (firstDependent, firstHead, secondDependent, secondHead)
  return none

/-- A well-formed dependency tree whose arcs do not cross in sentence order. -/
def Projective (heads : Array Nat) : Prop :=
  SentenceTreeWF heads ∧ firstCrossing? heads = none

instance (heads : Array Nat) : Decidable (Projective heads) := by
  unfold Projective
  infer_instance

/-- Validate general tree structure, then return the first crossing-arc witness if one exists. -/
def checkProjective (heads : Array Nat) : Except ProjectivityError Unit :=
  match checkSentenceTree heads with
  | .error cause => .error (.invalidTree cause)
  | .ok () =>
    match firstCrossing? heads with
    | none => .ok ()
    | some (firstDependent, firstHead, secondDependent, secondHead) =>
      .error (.crossing firstDependent firstHead secondDependent secondHead)

/-- The projectivity checker succeeds exactly for projective dependency trees. -/
theorem checkProjective_eq_ok_iff (heads : Array Nat) :
    checkProjective heads = .ok () ↔ Projective heads := by
  cases treeCheck : checkSentenceTree heads with
  | error cause => simp [checkProjective, Projective, SentenceTreeWF, treeCheck]
  | ok value =>
    cases value
    cases crossing : firstCrossing? heads with
    | none => simp [checkProjective, Projective, SentenceTreeWF, treeCheck, crossing]
    | some witness =>
      rcases witness with ⟨firstDependent, firstHead, secondDependent, secondHead⟩
      simp [checkProjective, Projective, SentenceTreeWF, treeCheck, crossing]

/-- A checked one-sentence dependency tree with one aligned relation value per dependent. -/
structure Tree (R : Type u) where
  private mk ::
  /-- Sentence-local 1-based heads, with `0` denoting the artificial root. -/
  heads : Array Nat
  /-- A relation value at each dependent position. -/
  relations : Array R
  /-- The relation column is positionally aligned with the head column. -/
  aligned : relations.size = heads.size
  /-- The stored heads form a general dependency tree; projectivity is not required. -/
  wellFormed : SentenceTreeWF heads

namespace Tree

/-- Validate aligned heads and relations and construct a checked dependency tree. -/
def ofArrays (heads : Array Nat) (relations : Array R) : Except TreeError (Tree R) :=
  if aligned : relations.size = heads.size then
    match checked : checkSentenceTree heads with
    | .ok () =>
      .ok ⟨heads, relations, aligned, (checkSentenceTree_eq_ok_iff heads).1 checked⟩
    | .error cause => .error cause
  else
    .error (.relationCount heads.size relations.size)

/-- Map relation values without changing heads or their checked tree structure. -/
def mapRelations (f : R → S) (tree : Tree R) : Tree S where
  heads := tree.heads
  relations := tree.relations.map f
  aligned := by simp [tree.aligned]
  wellFormed := tree.wellFormed

/-- Every checked tree has exactly one relation value per dependent. -/
@[simp] theorem relations_size (tree : Tree R) : tree.relations.size = tree.heads.size :=
  tree.aligned

end Tree

end Nlp.Dependency
