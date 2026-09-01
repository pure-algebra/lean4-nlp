import Std.Data.HashMap
import Nlp.Syntax.Tree

/-!
# Evaluation metrics

This module contains small, total evaluation kernels for tagging, labelled constituency
brackets, and conlleval-compatible chunks.  Span matching is multiset matching: each predicted
item can consume at most one equal gold item, so duplicate brackets are counted faithfully.
-/

namespace Nlp.Eval

/-- Micro-aggregateable true-positive, false-positive, and false-negative counts. -/
structure PRF where
  tp : Nat := 0
  fp : Nat := 0
  fn : Nat := 0
deriving Repr, DecidableEq, BEq, Inhabited

/-- Combine independent evaluation counts componentwise. -/
instance : Append PRF where
  append left right :=
    { tp := left.tp + right.tp
      fp := left.fp + right.fp
      fn := left.fn + right.fn }

/-- The neutral evaluation count. -/
instance : Zero PRF where
  zero := {}

/-- Convert a natural-number ratio to `Float`, returning zero for a zero denominator. -/
@[inline] def safeRatio (numerator denominator : Nat) : Float :=
  if denominator == 0 then 0.0 else Float.ofNat numerator / Float.ofNat denominator

/-- Micro precision, or zero when there are no predicted positives. -/
@[inline] def PRF.precision (score : PRF) : Float :=
  safeRatio score.tp (score.tp + score.fp)

/-- Micro recall, or zero when there are no gold positives. -/
@[inline] def PRF.recall (score : PRF) : Float :=
  safeRatio score.tp (score.tp + score.fn)

/-- Micro F1, or zero when both precision and recall are zero. -/
@[inline] def PRF.f1 (score : PRF) : Float :=
  let precision := score.precision
  let recall := score.recall
  let total := precision + recall
  if total == 0.0 then 0.0 else 2.0 * precision * recall / total

/--
Count positionwise correct tags against the gold length.

Missing predictions are incorrect; predictions beyond `gold.size` never add to the correct
count.  The returned total is always exactly `gold.size`.
-/
def taggingAccuracy (gold pred : Array String) : Nat × Nat := Id.run do
  let mut correct := 0
  for index in [0:gold.size] do
    match pred[index]? with
    | some predicted =>
        if predicted == gold[index]! then
          correct := correct + 1
    | none => pure ()
  return (correct, gold.size)

/-- Count a one-to-one multiset intersection, consuming each gold occurrence at most once. -/
private def multisetMatches {Item : Type} [BEq Item] [Inhabited Item]
    (gold pred : Array Item) : Nat := Id.run do
  let mut used := Array.replicate gold.size false
  let mut matchedCount := 0
  for predicted in pred do
    let mut matched := false
    for index in [0:gold.size] do
      if !matched && !(used[index]!) && gold[index]! == predicted then
        used := used.set! index true
        matched := true
    if matched then
      matchedCount := matchedCount + 1
  return matchedCount

/--
Score two arrays as multisets with exact equality and one-to-one matching.

The identical-array case records the lawful-equality identity directly; the general case uses
the same greedy one-to-one occurrence matching as before.
-/
def multisetScore {Item : Type} [BEq Item] [LawfulBEq Item] [Inhabited Item]
    (gold pred : Array Item) : PRF :=
  if gold == pred then
    { tp := gold.size }
  else
    let tp := multisetMatches gold pred
    { tp, fp := pred.size - tp, fn := gold.size - tp }

/--
Score two arrays as multisets by counting exact key multiplicities in a hash table.

This is the linear-expected-time implementation for lawful hashable keys. `multisetScore`
remains the generic equality-only reference implementation.
-/
def multisetScoreHash {Item : Type} [BEq Item] [LawfulBEq Item] [Hashable Item]
    (gold pred : Array Item) : PRF := Id.run do
  if gold == pred then
    return { tp := gold.size }
  let mut remaining : Std.HashMap Item Nat :=
    Std.HashMap.emptyWithCapacity gold.size
  for item in gold do
    remaining := remaining.insert item (remaining.getD item 0 + 1)
  let mut tp := 0
  for item in pred do
    let count := remaining.getD item 0
    if 0 < count then
      tp := tp + 1
      if count == 1 then
        remaining := remaining.erase item
      else
        remaining := remaining.insert item (count - 1)
  return { tp, fp := pred.size - tp, fn := gold.size - tp }

/-- Append raw nonterminal brackets to an output buffer and return the final fencepost. -/
def bracketsInto : Tree → Nat → Array (Cat × Nat × Nat) →
    Array (Cat × Nat × Nat) × Nat
  | .leaf _, start, output => (output, start + 1)
  | .node cat child children, start, output =>
      let isPreterminal :=
        match child with
        | .leaf _ => children.isEmpty
        | .node _ _ _ => false
      let rootIndex := output.size
      let output := if isPreterminal then output else output.push (cat, start, start)
      let (output, afterFirst) := bracketsInto child start output
      let (output, stop) := children.attach.foldl
        (fun (accumulator, offset) ⟨tree, _⟩ ↦ bracketsInto tree offset accumulator)
        (output, afterFirst)
      if isPreterminal then
        (output, stop)
      else
        (output.set! rootIndex (cat, start, stop), stop)

/-- Traverse a tree from a token offset, returning nonterminal brackets and the stop offset. -/
def bracketsFrom (tree : Tree) (start : Nat) : Array (Cat × Nat × Nat) × Nat :=
  bracketsInto tree start #[]

/--
Raw labelled nonterminal brackets in preorder.

Exactly preterminal nodes of shape `.node _ (.leaf _) #[]` are excluded.  Unary
nonterminals remain, including duplicate same-label brackets over the same span.
-/
def brackets (tree : Tree) : Array (Cat × Nat × Nat) :=
  (bracketsFrom tree 0).1

/-- Raw labelled nonterminal bracket score with one-to-one duplicate matching. -/
def bracketScore (gold pred : Tree) : PRF :=
  multisetScoreHash (brackets gold) (brackets pred)

/-- A conlleval tag split at its first hyphen. -/
structure ChunkTag where
  mark : String
  chunkType : String
deriving Repr, DecidableEq, BEq, Inhabited

private def splitTagChars : List Char → List Char → ChunkTag
  | [], reversedPrefix =>
      { mark := String.ofList reversedPrefix.reverse, chunkType := "" }
  | '-' :: suffix, reversedPrefix =>
      { mark := String.ofList reversedPrefix.reverse, chunkType := String.ofList suffix }
  | character :: suffix, reversedPrefix =>
      splitTagChars suffix (character :: reversedPrefix)

/--
Split a conlleval tag with the regex semantics `^([^-]*)-(.*)$`.

Only the first hyphen is structural, so `B-WORK-OF-ART` has prefix `B` and type
`WORK-OF-ART`.  A tag with no hyphen is entirely its prefix and has the empty type.
-/
def splitTag (label : String) : ChunkTag := splitTagChars label.toList []

@[inline] private def isOutside (mark : String) : Bool :=
  mark == "O" || mark == "."

/-- The exact conlleval `endOfChunk` transition predicate. -/
def endOfChunk (previous current : ChunkTag) : Bool :=
  let p := previous.mark
  let c := current.mark
  (p == "B" && c == "B") || (p == "B" && c == "O") ||
    (p == "I" && c == "B") || (p == "I" && c == "O") ||
    (p == "E" && c == "E") || (p == "E" && c == "I") ||
    (p == "E" && c == "O") ||
    (!isOutside p && previous.chunkType != current.chunkType) ||
    p == "]" || p == "["

/-- The exact conlleval `startOfChunk` transition predicate, including permissive IOB1. -/
def startOfChunk (previous current : ChunkTag) : Bool :=
  let p := previous.mark
  let c := current.mark
  (p == "B" && c == "B") || (p == "I" && c == "B") ||
    (p == "O" && c == "B") || (p == "O" && c == "I") ||
    (p == "E" && c == "E") || (p == "E" && c == "I") ||
    (p == "O" && c == "E") || (p == "O" && c == "I") ||
    (!isOutside c && previous.chunkType != current.chunkType) ||
    c == "[" || c == "]"

/--
Extract conlleval-compatible typed chunks as half-open token spans.

The previous tag initially has empty prefix and type, matching conlleval.  An open chunk is
flushed at end of input, and ill-formed IOB1/IOB2/IOE/bracket transitions retain the scorer's
permissive boundary semantics.
-/
def chunks (labels : Array String) : Array (Nat × Nat × String) := Id.run do
  let mut previous := splitTag ""
  let mut openChunk : Option (Nat × String) := none
  let mut output : Array (Nat × Nat × String) := #[]
  for index in [0:labels.size] do
    let current := splitTag labels[index]!
    if endOfChunk previous current then
      match openChunk with
      | some (start, chunkType) =>
          output := output.push (start, index, chunkType)
          openChunk := none
      | none => pure ()
    if startOfChunk previous current then
      openChunk := some (index, current.chunkType)
    previous := current
  match openChunk with
  | some (start, chunkType) =>
      output := output.push (start, labels.size, chunkType)
  | none => pure ()
  return output

/-- Exact span-and-type chunk score with duplicate-aware multiset matching. -/
def chunkScore (gold pred : Array String) : PRF :=
  multisetScoreHash (chunks gold) (chunks pred)

end Nlp.Eval
