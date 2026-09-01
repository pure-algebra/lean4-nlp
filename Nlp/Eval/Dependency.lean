import Nlp.Core.Data.Dependency
import Nlp.Eval

/-!
# Dependency attachment evaluation

This module computes checked unlabeled and labeled attachment counts over sentence-local CoNLL-U
heads. Dependents are the array positions `1 .. n`; artificial root `0` is not itself scored, but
the token attached to root is an ordinary scored dependent unless the punctuation policy excludes
it. Corpus scores are micro-aggregated by componentwise addition.
-/

namespace Nlp.Eval.Dependency

/-- Whether a validation failure came from the gold or predicted tree. -/
inductive Side where
  | gold
  | predicted
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Typed failures at dependency-evaluation boundaries. -/
inductive Error where
  /-- One side does not contain aligned relations and a general dependency tree. -/
  | tree (side : Side) (cause : Nlp.Dependency.TreeError)
  /-- Gold and prediction contain different numbers of dependents. -/
  | tokenCountMismatch (gold predicted : Nat)
  /-- The gold POS column is not aligned with its dependents. -/
  | posCountMismatch (expected found : Nat)
  /-- Gold and predicted corpora contain different numbers of sentences. -/
  | sentenceCountMismatch (gold predicted : Nat)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Micro-additive unlabeled and labeled attachment counts. -/
structure Counts where
  /-- Number of dependents retained by the punctuation policy. -/
  total : Nat := 0
  /-- Retained dependents whose predicted head equals the gold head. -/
  uasCorrect : Nat := 0
  /-- Retained dependents whose head and dependency relation both match. -/
  lasCorrect : Nat := 0
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Combine independent attachment counts componentwise. -/
instance : Append Counts where
  append left right := {
    total := left.total + right.total
    uasCorrect := left.uasCorrect + right.uasCorrect
    lasCorrect := left.lasCorrect + right.lasCorrect
  }

/-- The neutral attachment count. -/
instance : Zero Counts where
  zero := {}

namespace Counts

/-- Unlabeled attachment accuracy, or zero when the punctuation policy retains no dependents. -/
@[inline] def uas (counts : Counts) : Float :=
  safeRatio counts.uasCorrect counts.total

/-- Labeled attachment accuracy, or zero when the punctuation policy retains no dependents. -/
@[inline] def las (counts : Counts) : Float :=
  safeRatio counts.lasCorrect counts.total

end Counts

/-- A token-retention policy receiving a zero-based array index and the gold POS tag. -/
structure PunctuationPolicy where
  keepToken : Nat → String → Bool

namespace PunctuationPolicy

/-- Score every dependent, including punctuation and the token attached to root. -/
def includeAll : PunctuationPolicy where
  keepToken := fun _ _ ↦ true

/-- Exclude exactly those dependents whose gold POS tag satisfies a caller predicate. -/
def excludeByPos (isPunctuation : String → Bool) : PunctuationPolicy where
  keepToken := fun _ pos ↦ !isPunctuation pos

end PunctuationPolicy

/-- Raw gold columns for one sentence; checking occurs at the scorer boundary. -/
structure GoldSentence (R : Type u) where
  heads : Array Nat
  relations : Array R
  pos : Array String
  deriving Inhabited

/-- Raw predicted columns for one sentence; checking occurs at the scorer boundary. -/
structure PredictedSentence (R : Type u) where
  heads : Array Nat
  relations : Array R
  deriving Inhabited

/-- Adapt checked-tree construction while retaining which evaluation side failed. -/
private def checkTree (side : Side) (heads : Array Nat) (relations : Array R) :
    Except Error (Nlp.Dependency.Tree R) :=
  match Nlp.Dependency.Tree.ofArrays heads relations with
  | .ok tree => .ok tree
  | .error cause => .error (.tree side cause)

/--
Score two already checked trees with one aligned gold POS column.

LAS requires both the head and relation to match. The artificial root is not an array position;
a dependent whose gold head is `0` is scored normally when retained by `policy`.
-/
def scoreCheckedWith [BEq R] (policy : PunctuationPolicy) (pos : Array String)
    (gold predicted : Nlp.Dependency.Tree R) : Except Error Counts := do
  unless gold.heads.size == predicted.heads.size do
    throw (.tokenCountMismatch gold.heads.size predicted.heads.size)
  unless pos.size == gold.heads.size do
    throw (.posCountMismatch gold.heads.size pos.size)
  let mut counts : Counts := {}
  for index in [0:gold.heads.size] do
    if policy.keepToken index pos[index]! then
      counts := { counts with total := counts.total + 1 }
      if gold.heads[index]! == predicted.heads[index]! then
        counts := { counts with uasCorrect := counts.uasCorrect + 1 }
        match gold.relations[index]?, predicted.relations[index]? with
        | some goldRelation, some predictedRelation =>
          if goldRelation == predictedRelation then
            counts := { counts with lasCorrect := counts.lasCorrect + 1 }
        | _, _ => pure ()
  return counts

/-- Validate and score one sentence under an explicit punctuation policy. -/
def scoreSentenceWith [BEq R] (policy : PunctuationPolicy)
    (gold : GoldSentence R) (predicted : PredictedSentence R) : Except Error Counts := do
  let checkedGold ← checkTree .gold gold.heads gold.relations
  let checkedPredicted ← checkTree .predicted predicted.heads predicted.relations
  scoreCheckedWith policy gold.pos checkedGold checkedPredicted

/-- Validate and score one sentence while including every dependent. -/
@[inline] def scoreSentence [BEq R] (gold : GoldSentence R)
    (predicted : PredictedSentence R) : Except Error Counts :=
  scoreSentenceWith .includeAll gold predicted

/-- Validate aligned sentence pairs and micro-aggregate their attachment counts. -/
def scoreCorpusWith [BEq R] (policy : PunctuationPolicy)
    (gold : Array (GoldSentence R)) (predicted : Array (PredictedSentence R)) :
    Except Error Counts := do
  unless gold.size == predicted.size do
    throw (.sentenceCountMismatch gold.size predicted.size)
  let mut counts : Counts := 0
  for index in [0:gold.size] do
    counts := counts ++ (← scoreSentenceWith policy gold[index]! predicted[index]!)
  return counts

/-- Validate and micro-aggregate a corpus while including every dependent. -/
@[inline] def scoreCorpus [BEq R] (gold : Array (GoldSentence R))
    (predicted : Array (PredictedSentence R)) : Except Error Counts :=
  scoreCorpusWith .includeAll gold predicted

end Nlp.Eval.Dependency
