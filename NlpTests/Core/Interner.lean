import Nlp.Core.Data.InternerLemmas

namespace NlpTests.Core.Interner

open Nlp

private def built : Except Interner.Error (Interner × UInt32 × UInt32 × UInt32) := do
  let (afterDog, dog) ← Interner.empty.intern "dog"
  let (afterCat, cat) ← afterDog.intern "cat"
  let (afterDogAgain, dogAgain) ← afterCat.intern "dog"
  pure (afterDogAgain, dog, cat, dogAgain)

private def lookupRoundTrips : Bool :=
  match built with
  | .ok (interner, dog, cat, dogAgain) =>
    dog == 0 && cat == 1 && dogAgain == dog &&
      interner.lookup? "dog" == some dog && interner.name? dog == some "dog" &&
      interner.lookup? "cat" == some cat && interner.name? cat == some "cat"
  | .error _ => false

#guard lookupRoundTrips

/- Persistence: inserting into the returned value does not mutate the source value. -/
#guard Interner.empty.lookup? "dog" == none

private def oneEntry : Interner.Capacity := ⟨1, by decide⟩

private def capacityIsExplicit : Bool :=
  match Interner.empty.internWith oneEntry "dog" with
  | .error _ => false
  | .ok (full, dog) =>
    match full.internWith oneEntry "dog", full.internWith oneEntry "cat" with
    | .ok (_, dogAgain), .error (.capacityExceeded 1) => dogAgain == dog
    | _, _ => false

#guard capacityIsExplicit

#guard (Interner.Capacity.ofNat? UInt32.size).isSome
#guard (Interner.Capacity.ofNat? (UInt32.size + 1)).isNone

example : Interner.empty.WF := Interner.empty_wf

example (interner : Interner) (name : String) (id : UInt32)
    (found : interner.lookup? name = some id) :
    interner.intern name = .ok (interner, id) :=
  Interner.intern_of_lookup?_eq_some interner name id found

example (interner next : Interner) (name : String) (id : UInt32)
    (wellFormed : interner.WF)
    (success : interner.intern name = .ok (next, id)) :
    next.WF ∧ interner.size ≤ next.size ∧
      next.lookup? name = some id ∧ next.name? id = some name := by
  exact ⟨Interner.wf_of_intern_eq_ok interner next name id wellFormed success,
    Interner.size_le_of_intern_eq_ok interner next name id success,
    Interner.lookup?_intern_eq_ok interner next name id success,
    Interner.name?_intern_eq_ok interner next name id wellFormed success⟩

example (interner next : Interner) (name : String) (id : UInt32)
    (fresh : interner.lookup? name = none)
    (success : interner.intern name = .ok (next, id)) :
    id = UInt32.ofNat interner.size ∧ next.name? id = some name := by
  exact ⟨Interner.intern_fresh_id interner next name id fresh success,
    Interner.name?_intern_fresh_eq_ok interner next name id fresh success⟩

end NlpTests.Core.Interner
