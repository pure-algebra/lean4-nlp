import Init.Data.Array.Lemmas

/-!
# Total `FloatArray` utilities

Lean core provides the unboxed `FloatArray` representation and primitive operations, but almost
no supporting lemmas.  This module supplies the constructors, safe defaulting read, and size
facts needed by dense NLP charts without adding Batteries or Mathlib.
-/

namespace FloatArray

/-- Construct an unboxed float array from an ordinary array. -/
@[inline] def ofArray (values : Array Float) : FloatArray := ⟨values⟩

@[simp] theorem size_mk (values : Array Float) : (FloatArray.mk values).size = values.size := rfl

@[simp] theorem size_ofArray (values : Array Float) : (ofArray values).size = values.size := rfl

@[simp] theorem size_emptyWithCapacity (capacity : Nat) :
    (FloatArray.emptyWithCapacity capacity).size = 0 := rfl

@[simp] theorem size_empty : FloatArray.empty.size = 0 := rfl

@[simp] theorem size_push (values : FloatArray) (value : Float) :
    (values.push value).size = values.size + 1 := by
  cases values
  simp [FloatArray.push, FloatArray.size]

@[simp] theorem size_set (values : FloatArray) (index : Nat) (value : Float)
    (inBounds : index < values.size) :
    (values.set index value inBounds).size = values.size := by
  cases values with
  | mk data => exact Array.size_set inBounds

@[simp] theorem size_uset (values : FloatArray) (index : USize) (value : Float)
    (inBounds : index.toNat < values.size) :
    (values.uset index value inBounds).size = values.size := by
  cases values with
  | mk data =>
      change index.toNat < data.size at inBounds
      exact Array.size_uset inBounds

@[simp] theorem size_set! (values : FloatArray) (index : Nat) (value : Float) :
    (values.set! index value).size = values.size := by
  cases values
  simp [FloatArray.set!, FloatArray.size]

/-- Reading the location just written by a checked update returns the new value. -/
@[simp] theorem get_set (values : FloatArray) (index : Nat) (value : Float)
    (inBounds : index < values.size) :
    (values.set index value inBounds).get index (by simpa using inBounds) = value := by
  cases values with
  | mk data =>
      change index < data.size at inBounds
      exact Array.getElem_set_self inBounds

/-- A checked `USize` update refines to the ordinary checked update at the same index. -/
theorem uset_eq_set (values : FloatArray) (index : USize) (value : Float)
    (inBounds : index.toNat < values.size) :
    values.uset index value inBounds = values.set index.toNat value inBounds := by
  cases values with
  | mk data =>
      change index.toNat < data.size at inBounds
      exact congrArg FloatArray.mk (Array.uset_eq_set inBounds)

/-- Reading the location just written by a checked `USize` update returns the new value. -/
@[simp] theorem get_uset (values : FloatArray) (index : USize) (value : Float)
    (inBounds : index.toNat < values.size) :
    (values.uset index value inBounds).uget index (by simpa using inBounds) = value := by
  cases values with
  | mk data =>
      change index.toNat < data.size at inBounds
      have updatedBounds : index.toNat < (data.uset index value inBounds).size := by
        simpa using inBounds
      have result : (data.uset index value inBounds)[index.toNat]'updatedBounds = value := by
        simpa only [Array.uset_eq_set] using
          (Array.getElem_set_self (xs := data) inBounds (v := value))
      exact result

/-- In bounds, the unchecked-boundary `set!` has exactly the checked `set` result. -/
theorem set!_eq_set (values : FloatArray) (index : Nat) (value : Float)
    (inBounds : index < values.size) :
    values.set! index value = values.set index value inBounds := by
  cases values with
  | mk data =>
      change index < data.size at inBounds
      apply congrArg FloatArray.mk
      rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
      simp only [inBounds, dite_true]

/-- Reading an in-bounds location just written by `set!` returns the new value. -/
@[simp] theorem get_set! (values : FloatArray) (index : Nat) (value : Float)
    (inBounds : index < values.size) :
    (values.set! index value).get index (by simpa using inBounds) = value := by
  cases values with
  | mk data =>
      change index < data.size at inBounds
      have updatedBounds : index < (data.set! index value).size := by
        simpa using inBounds
      have result : (data.set! index value)[index]'updatedBounds = value := by
        have ifBounds : index < (data.setIfInBounds index value).size := by
          simpa using inBounds
        simpa only [Array.set!_eq_setIfInBounds] using
          (Array.getElem_setIfInBounds_self ifBounds)
      exact result

/-- Tail-recursive worker for `replicate`. -/
def replicateGo (value : Float) : Nat → FloatArray → FloatArray
  | 0, accumulator => accumulator
  | count + 1, accumulator => replicateGo value count (accumulator.push value)

/-- Construct an unboxed array containing `count` copies of `value`. -/
def replicate (count : Nat) (value : Float) : FloatArray :=
  replicateGo value count (FloatArray.emptyWithCapacity count)

@[simp] theorem size_replicateGo (value : Float) (count : Nat) (accumulator : FloatArray) :
    (replicateGo value count accumulator).size = accumulator.size + count := by
  induction count generalizing accumulator with
  | zero => simp [replicateGo]
  | succ count inductionHypothesis =>
      simp [replicateGo, inductionHypothesis]
      omega

@[simp] theorem size_replicate (count : Nat) (value : Float) :
    (replicate count value).size = count := by
  simp [replicate]

/-- Read an element when it is in bounds and otherwise return the caller-supplied default. -/
@[inline] def getD (values : FloatArray) (index : Nat) (default : Float) : Float :=
  if inBounds : index < values.size then values.get index inBounds else default

@[simp] theorem getD_eq_get (values : FloatArray) (index : Nat) (default : Float)
    (inBounds : index < values.size) :
    values.getD index default = values.get index inBounds := by
  simp [getD, inBounds]

@[simp] theorem getD_eq_default (values : FloatArray) (index : Nat) (default : Float)
    (outOfBounds : ¬index < values.size) :
    values.getD index default = default := by
  simp [getD, outOfBounds]

end FloatArray
