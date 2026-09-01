import Std.Data.HashMap

/-!
# Persistent string interning

`Interner` grows a persistent bijection between strings and dense `UInt32` identifiers. New IDs
are allocated from `names.size`; insertion checks capacity before `UInt32.ofNat`, so exhaustion is
a typed error rather than a silent wrap at `2^32`.
-/

namespace Nlp

/-- A persistent string-to-identifier table with a reverse dense array. -/
structure Interner where
  ids : Std.HashMap String UInt32 := {}
  names : Array String := #[]

namespace Interner

/-- An allocation limit proven to fit in the `UInt32` identifier space. -/
structure Capacity where
  limit : Nat
  fitsUInt32 : limit ≤ UInt32.size

namespace Capacity

/-- The complete `UInt32` identifier space, containing IDs `0` through `2^32 - 1`. -/
def uint32 : Capacity := ⟨UInt32.size, Nat.le_refl _⟩

/-- Validate a smaller application-specific vocabulary limit. -/
def ofNat? (limit : Nat) : Option Capacity :=
  if fits : limit ≤ UInt32.size then some ⟨limit, fits⟩ else none

end Capacity

/-- Interning cannot allocate another distinct name within the selected capacity. -/
inductive Error where
  | capacityExceeded (limit : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The empty interner. -/
def empty : Interner := {}

/-- Number of distinct interned names. -/
@[inline] def size (interner : Interner) : Nat := interner.names.size

/-- Look up the ID already assigned to a name. -/
@[inline] def lookup? (interner : Interner) (name : String) : Option UInt32 :=
  interner.ids.get? name

/-- Resolve an ID to its name. -/
@[inline] def name? (interner : Interner) (id : UInt32) : Option String :=
  interner.names[id.toNat]?

/-- Intern a name under an explicit checked capacity.

Existing names remain available after capacity is reached. Only allocation of a new distinct name
can fail.
-/
def internWith (capacity : Capacity) (interner : Interner) (name : String) :
    Except Error (Interner × UInt32) :=
  match interner.lookup? name with
  | some id => .ok (interner, id)
  | none =>
    if _room : interner.size < capacity.limit then
      let id := UInt32.ofNat interner.size
      .ok (⟨interner.ids.insert name id, interner.names.push name⟩, id)
    else
      .error (.capacityExceeded capacity.limit)

/-- Intern a name using the complete `UInt32` identifier space. -/
@[inline] def intern (interner : Interner) (name : String) : Except Error (Interner × UInt32) :=
  internWith .uint32 interner name

/-- The forward map resolves through the reverse array. -/
def WF (interner : Interner) : Prop :=
  ∀ name id, interner.lookup? name = some id → interner.name? id = some name

/-- Forward lookup followed by reverse lookup is a round trip for a well-formed interner. -/
theorem name?_lookup? (interner : Interner) (wellFormed : interner.WF)
    (name : String) (id : UInt32) (found : interner.lookup? name = some id) :
    interner.name? id = some name :=
  wellFormed name id found

end Interner

end Nlp
