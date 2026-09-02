/-!
# Stable packed buckets

This module builds a stable counting-sort layout without allocating or default-initializing any
caller payload columns. The private layout constructor keeps offsets and source ordinals aligned.
-/

namespace Nlp.StableBuckets

/-- Explicit allocation limits for one packed-bucket layout. -/
structure Limits where
  maxBuckets : Nat
  maxEntries : Nat
deriving Repr, DecidableEq, Inhabited

/-- Why a stable packed-bucket layout could not be built or projected. -/
inductive Error where
  /-- The requested bucket count exceeds the caller's policy limit. -/
  | bucketBudget (required limit : Nat)
  /-- The source entry count exceeds the caller's policy limit. -/
  | entryBudget (required limit : Nat)
  /-- The terminal offset would exceed the runtime's array-size representation. -/
  | offsetCapacity (bucketCount : Nat)
  /-- One source entry selected a bucket outside `[0, bucketCount)`. -/
  | invalidBucket (source bucket bucketCount : Nat)
  /-- A projected parallel column does not have the layout's source entry count. -/
  | columnSize (expected actual : Nat)
deriving Repr, DecidableEq, Inhabited

/-- A checked half-open range occupied by one bucket. Empty buckets have an empty range. -/
structure BucketRange where
  private mk ::
  first : Nat
  stop : Nat
deriving Repr, DecidableEq

namespace BucketRange

/-- Number of entries in a checked bucket range. -/
@[inline] def size (range : BucketRange) : Nat :=
  range.stop - range.first

end BucketRange

/--
Stable source ordinals grouped into contiguous buckets.

`offsets` has exactly one terminal sentinel, and `sourceOrder` is a stable permutation of every
source ordinal. The private constructor ensures those invariants can only be established here.
-/
structure Layout where
  private mk ::
  bucketCount : Nat
  entryCount : Nat
  offsets : Array Nat
  sourceOrder : Array Nat
deriving Repr, DecidableEq

namespace Layout

/-- Return the checked half-open range for a valid bucket, including valid empty buckets. -/
@[inline] def range? (layout : Layout) (bucket : Nat) : Option BucketRange :=
  if bucket < layout.bucketCount then
    match layout.offsets[bucket]?, layout.offsets[bucket + 1]? with
    | some first, some stop =>
        if first ≤ stop ∧ stop ≤ layout.entryCount then some ⟨first, stop⟩ else none
    | _, _ => none
  else
    none

/--
Project a source-aligned column into stable bucket order without requiring a default value.
-/
def gatherMap (layout : Layout) (column : Array α) (project : α → β) :
    Except Error (Array β) := do
  unless column.size = layout.entryCount do
    throw <| .columnSize layout.entryCount column.size
  let mut output := Array.emptyWithCapacity layout.entryCount
  for source in layout.sourceOrder do
    match column[source]? with
    | some value => output := output.push (project value)
    | none => throw <| .columnSize layout.entryCount column.size
  return output

end Layout

/--
Build stable contiguous buckets from one source array.

All policy, offset-capacity, and key checks finish before bucket-driven arrays are allocated. The
first invalid source ordinal is reported deterministically. The key function is then evaluated
again during counting and stable filling.
-/
@[inline] def build (limits : Limits) (bucketCount : Nat) (source : Array α) (bucketOf : α → Nat) :
    Except Error Layout := do
  if limits.maxBuckets < bucketCount then
    throw <| .bucketBudget bucketCount limits.maxBuckets
  if limits.maxEntries < source.size then
    throw <| .entryBudget source.size limits.maxEntries
  unless bucketCount + 1 < USize.size do
    throw <| .offsetCapacity bucketCount
  let mut sourceIndex := 0
  for item in source do
    let bucket := bucketOf item
    unless bucket < bucketCount do
      throw <| .invalidBucket sourceIndex bucket bucketCount
    sourceIndex := sourceIndex + 1

  let mut counts := Array.replicate bucketCount 0
  for item in source do
    let bucket := bucketOf item
    counts := counts.modify bucket (fun count ↦ count + 1)

  let mut offsets := Array.emptyWithCapacity (bucketCount + 1)
  let mut cursors := counts
  let mut total := 0
  for bucket in [0:bucketCount] do
    offsets := offsets.push total
    let count := cursors[bucket]!
    cursors := cursors.set! bucket total
    total := total + count
  offsets := offsets.push total

  let mut sourceOrder := Array.replicate source.size 0
  sourceIndex := 0
  for item in source do
    let bucket := bucketOf item
    let target := cursors[bucket]!
    sourceOrder := sourceOrder.set! target sourceIndex
    cursors := cursors.set! bucket (target + 1)
    sourceIndex := sourceIndex + 1
  return .mk bucketCount source.size offsets sourceOrder

end Nlp.StableBuckets
