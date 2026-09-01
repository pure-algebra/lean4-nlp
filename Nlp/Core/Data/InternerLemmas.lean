import Nlp.Core.Data.Interner
import Std.Data.HashMap.Lemmas

/-!
# Persistent interner laws

The runtime representation remains proof-free. These boundary lemmas establish that successful
interning preserves the forward/reverse invariant and all previously observable bindings.
-/

namespace Nlp.Interner

/-- The empty interner satisfies the forward-to-reverse invariant. -/
theorem empty_wf : empty.WF := by
  simp [WF, empty, lookup?]

/-- Interning an existing name returns the original state and identifier. -/
theorem internWith_of_lookup?_eq_some (capacity : Capacity) (interner : Interner)
    (name : String) (id : UInt32) (found : interner.lookup? name = some id) :
    interner.internWith capacity name = .ok (interner, id) := by
  simp [internWith, found]

/-- The default-capacity operation also leaves an existing binding unchanged. -/
theorem intern_of_lookup?_eq_some (interner : Interner) (name : String) (id : UInt32)
    (found : interner.lookup? name = some id) :
    interner.intern name = .ok (interner, id) := by
  exact internWith_of_lookup?_eq_some .uint32 interner name id found

/-- A fresh successful insertion uses the current reverse-array size as its dense identifier. -/
theorem internWith_of_lookup?_eq_none (capacity : Capacity) (interner : Interner)
    (name : String) (fresh : interner.lookup? name = none)
    (room : interner.size < capacity.limit) :
    interner.internWith capacity name =
      .ok (⟨interner.ids.insert name (UInt32.ofNat interner.size),
        interner.names.push name⟩, UInt32.ofNat interner.size) := by
  simp [internWith, fresh, room]

/-- Any successful fresh insertion returns exactly the dense identifier at the old size. -/
theorem internWith_fresh_id (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32) (fresh : interner.lookup? name = none)
    (success : interner.internWith capacity name = .ok (next, id)) :
    id = UInt32.ofNat interner.size := by
  by_cases room : interner.size < capacity.limit
  · rw [internWith_of_lookup?_eq_none capacity interner name fresh room] at success
    cases success
    rfl
  · simp [internWith, fresh, room] at success

/-- A fresh successful insertion installs the new reverse binding without extra assumptions. -/
theorem name?_internWith_fresh_eq_ok (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32) (fresh : interner.lookup? name = none)
    (success : interner.internWith capacity name = .ok (next, id)) :
    next.name? id = some name := by
  by_cases room : interner.size < capacity.limit
  · rw [internWith_of_lookup?_eq_none capacity interner name fresh room] at success
    obtain ⟨rfl, rfl⟩ := success
    have bound : interner.size < UInt32.size :=
      Nat.lt_of_lt_of_le room capacity.fitsUInt32
    change (interner.names.push name)[(UInt32.ofNat interner.size).toNat]? = some name
    rw [UInt32.toNat_ofNat_of_lt' bound]
    exact Array.getElem?_push_size
  · simp [internWith, fresh, room] at success

/-- Successful interning never decreases the vocabulary size. -/
theorem size_le_of_internWith_eq_ok (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32)
    (success : interner.internWith capacity name = .ok (next, id)) :
    interner.size ≤ next.size := by
  cases found : interner.lookup? name with
  | some existing =>
    simp [internWith, found] at success
    obtain ⟨rfl, rfl⟩ := success
    exact Nat.le_refl _
  | none =>
    by_cases room : interner.size < capacity.limit
    · simp [internWith, found, room] at success
      obtain ⟨rfl, rfl⟩ := success
      simp [size]
    · simp [internWith, found, room] at success

/-- Successful interning preserves every pre-existing forward binding. -/
theorem lookup?_of_internWith_eq_ok (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32)
    (success : interner.internWith capacity name = .ok (next, id))
    (oldName : String) (oldId : UInt32)
    (found : interner.lookup? oldName = some oldId) :
    next.lookup? oldName = some oldId := by
  cases current : interner.lookup? name with
  | some existing =>
    simp [internWith, current] at success
    obtain ⟨rfl, rfl⟩ := success
    exact found
  | none =>
    by_cases room : interner.size < capacity.limit
    · simp [internWith, current, room] at success
      obtain ⟨rfl, rfl⟩ := success
      have different : name ≠ oldName := by
        intro same
        subst same
        rw [current] at found
        contradiction
      change interner.ids[oldName]? = some oldId at found
      change (interner.ids.insert name (UInt32.ofNat interner.size))[oldName]? = some oldId
      rw [Std.HashMap.getElem?_insert]
      simp [different, found]
    · simp [internWith, current, room] at success

/-- Successful interning preserves every pre-existing reverse binding. -/
theorem name?_of_internWith_eq_ok (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32)
    (success : interner.internWith capacity name = .ok (next, id))
    (oldId : UInt32) (oldName : String) (found : interner.name? oldId = some oldName) :
    next.name? oldId = some oldName := by
  cases current : interner.lookup? name with
  | some existing =>
    simp [internWith, current] at success
    obtain ⟨rfl, rfl⟩ := success
    exact found
  | none =>
    by_cases room : interner.size < capacity.limit
    · simp [internWith, current, room] at success
      obtain ⟨rfl, rfl⟩ := success
      change interner.names[oldId.toNat]? = some oldName at found
      change (interner.names.push name)[oldId.toNat]? = some oldName
      rw [Array.getElem?_push]
      have different : oldId.toNat ≠ interner.names.size := by
        intro same
        rw [same] at found
        simp at found
      simp [different, found]
    · simp [internWith, current, room] at success

/-- The requested name resolves to the identifier returned by every successful operation. -/
theorem lookup?_internWith_eq_ok (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32)
    (success : interner.internWith capacity name = .ok (next, id)) :
    next.lookup? name = some id := by
  cases current : interner.lookup? name with
  | some existing =>
    simp [internWith, current] at success
    obtain ⟨rfl, rfl⟩ := success
    exact current
  | none =>
    by_cases room : interner.size < capacity.limit
    · simp [internWith, current, room] at success
      obtain ⟨rfl, rfl⟩ := success
      change (interner.ids.insert name (UInt32.ofNat interner.size))[name]? =
        some (UInt32.ofNat interner.size)
      exact Std.HashMap.getElem?_insert_self
    · simp [internWith, current, room] at success

/-- Successful interning preserves the forward-to-reverse invariant. -/
theorem wf_of_internWith_eq_ok (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32) (wellFormed : interner.WF)
    (success : interner.internWith capacity name = .ok (next, id)) : next.WF := by
  cases current : interner.lookup? name with
  | some existing =>
    simp [internWith, current] at success
    obtain ⟨rfl, rfl⟩ := success
    exact wellFormed
  | none =>
    by_cases room : interner.size < capacity.limit
    · simp [internWith, current, room] at success
      obtain ⟨rfl, rfl⟩ := success
      intro queried queriedId found
      change (interner.ids.insert name (UInt32.ofNat interner.size))[queried]? =
        some queriedId at found
      rw [Std.HashMap.getElem?_insert] at found
      by_cases same : name = queried
      · subst queried
        simp at found
        cases found
        have bound : interner.size < UInt32.size :=
          Nat.lt_of_lt_of_le room capacity.fitsUInt32
        change (interner.names.push name)[(UInt32.ofNat interner.size).toNat]? = some name
        rw [UInt32.toNat_ofNat_of_lt' bound]
        exact Array.getElem?_push_size
      · have oldFound : interner.lookup? queried = some queriedId := by
          change interner.ids[queried]? = some queriedId
          simpa [same] using found
        have reverse := wellFormed queried queriedId oldFound
        exact name?_of_internWith_eq_ok capacity interner
          { ids := interner.ids.insert name (UInt32.ofNat interner.size),
            names := interner.names.push name }
          name (UInt32.ofNat interner.size)
          (internWith_of_lookup?_eq_none capacity interner name current room)
          queriedId queried reverse
    · simp [internWith, current, room] at success

/-- The newly requested binding is a forward/reverse round trip from a well-formed source. -/
theorem name?_internWith_eq_ok (capacity : Capacity) (interner next : Interner)
    (name : String) (id : UInt32) (wellFormed : interner.WF)
    (success : interner.internWith capacity name = .ok (next, id)) :
    next.name? id = some name := by
  exact wf_of_internWith_eq_ok capacity interner next name id wellFormed success
    name id (lookup?_internWith_eq_ok capacity interner next name id success)

/-- Default-capacity interning preserves the forward-to-reverse invariant. -/
theorem wf_of_intern_eq_ok (interner next : Interner) (name : String) (id : UInt32)
    (wellFormed : interner.WF)
    (success : interner.intern name = .ok (next, id)) : next.WF := by
  exact wf_of_internWith_eq_ok .uint32 interner next name id wellFormed success

/-- A name resolves to the identifier returned by successful default-capacity interning. -/
theorem lookup?_intern_eq_ok (interner next : Interner) (name : String) (id : UInt32)
    (success : interner.intern name = .ok (next, id)) :
    next.lookup? name = some id := by
  exact lookup?_internWith_eq_ok .uint32 interner next name id success

/-- Successful default-capacity interning extends the reverse round trip. -/
theorem name?_intern_eq_ok (interner next : Interner) (name : String) (id : UInt32)
    (wellFormed : interner.WF)
    (success : interner.intern name = .ok (next, id)) :
    next.name? id = some name := by
  exact name?_internWith_eq_ok .uint32 interner next name id wellFormed success

/-- Successful default-capacity interning never decreases the vocabulary size. -/
theorem size_le_of_intern_eq_ok (interner next : Interner) (name : String) (id : UInt32)
    (success : interner.intern name = .ok (next, id)) :
    interner.size ≤ next.size := by
  exact size_le_of_internWith_eq_ok .uint32 interner next name id success

/-- A fresh default-capacity insertion returns the dense identifier at the old size. -/
theorem intern_fresh_id (interner next : Interner) (name : String) (id : UInt32)
    (fresh : interner.lookup? name = none)
    (success : interner.intern name = .ok (next, id)) :
    id = UInt32.ofNat interner.size := by
  exact internWith_fresh_id .uint32 interner next name id fresh success

/-- A fresh default-capacity insertion installs its new reverse binding. -/
theorem name?_intern_fresh_eq_ok (interner next : Interner) (name : String) (id : UInt32)
    (fresh : interner.lookup? name = none)
    (success : interner.intern name = .ok (next, id)) :
    next.name? id = some name := by
  exact name?_internWith_fresh_eq_ok .uint32 interner next name id fresh success

end Nlp.Interner
