/-!
# Typed regular token patterns

This module gives regular token languages a small typed syntax and two deliberately simple
semantics. `Regular.Accepts` is the denotational relation used by proofs. `Regular.endpoints` is a
finite executable reference matcher used to validate compiled automata. Both consume symbolic
atoms through `holdsAt`, so neither representation owns or slices the underlying token column.
-/

namespace Nlp.Pattern

/-- A half-open range in one symbolic input column. -/
structure Range where
  /-- Inclusive input position. -/
  start : Nat
  /-- Exclusive input position. -/
  stop : Nat
  deriving Repr, DecidableEq, Inhabited

namespace Range

/-- Number of positions in a normalized half-open range. -/
@[inline] def width (range : Range) : Nat :=
  range.stop - range.start

end Range

/--
Clamp a caller-selected range to an input size.

An inverted range collapses at its clamped upper endpoint. This convention agrees with the other
range APIs in the library and never requires allocating an input slice.
-/
@[inline] def normalizeRange (size start stop : Nat) : Range :=
  let upper := min stop size
  ⟨min start upper, upper⟩

/-- A normalized range always starts at or before its stop. -/
theorem normalizeRange_start_le_stop (size start stop : Nat) :
    (normalizeRange size start stop).start ≤ (normalizeRange size start stop).stop := by
  exact Nat.min_le_right _ _

/-- A normalized range never stops beyond the symbolic input. -/
theorem normalizeRange_stop_le_size (size start stop : Nat) :
    (normalizeRange size start stop).stop ≤ size := by
  exact Nat.min_le_right _ _

/-- Typed regular languages over symbolic token predicates. -/
inductive Regular (Atom : Type u) where
  /-- The language with no accepted ranges. -/
  | empty
  /-- The language containing only the empty range. -/
  | epsilon
  /-- One input position satisfying the supplied symbolic atom. -/
  | atom (value : Atom)
  /-- Ordered choice between two languages. -/
  | alt (left right : Regular Atom)
  /-- Concatenation of two languages. -/
  | seq (left right : Regular Atom)
  /-- Finite repetition, including zero repetitions. -/
  | star (body : Regular Atom)
  deriving Repr, DecidableEq

namespace Regular

/-- Decide whether a pattern accepts an empty range. -/
def nullable : Regular Atom → Bool
  | .empty => false
  | .epsilon => true
  | .atom _ => false
  | .alt left right => left.nullable || right.nullable
  | .seq left right => left.nullable && right.nullable
  | .star _ => true

/--
Denotational acceptance over absolute symbolic-input positions.

The relation has no constructor for `empty`. Atom acceptance advances by exactly one position;
concatenation records its split point; star records each finite repetition explicitly.
-/
inductive Accepts (holdsAt : Atom → Nat → Bool) : Regular Atom → Nat → Nat → Prop where
  /-- Epsilon accepts exactly an empty range. -/
  | epsilon (position : Nat) : Accepts holdsAt .epsilon position position
  /-- An atom consumes one position when its symbolic predicate holds there. -/
  | atom (value : Atom) (position : Nat) (holds : holdsAt value position = true) :
      Accepts holdsAt (.atom value) position (position + 1)
  /-- The left alternative preserves acceptance. -/
  | altLeft (accepted : Accepts holdsAt left start stop) :
      Accepts holdsAt (.alt left right) start stop
  /-- The right alternative preserves acceptance. -/
  | altRight (accepted : Accepts holdsAt right start stop) :
      Accepts holdsAt (.alt left right) start stop
  /-- Concatenation accepts when both pieces meet at one split point. -/
  | seq (leftAccepted : Accepts holdsAt left start middle)
      (rightAccepted : Accepts holdsAt right middle stop) :
      Accepts holdsAt (.seq left right) start stop
  /-- Star accepts zero repetitions. -/
  | starNil (body : Regular Atom) (position : Nat) :
      Accepts holdsAt (.star body) position position
  /-- Star accepts one body occurrence followed by finitely many more. -/
  | starCons (head : Accepts holdsAt body start middle)
      (tail : Accepts holdsAt (.star body) middle stop) :
      Accepts holdsAt (.star body) start stop

/-- Denotational regular matching never moves an input position backwards. -/
theorem Accepts.start_le_stop (accepted : Accepts holdsAt pattern start stop) : start ≤ stop := by
  induction accepted with
  | epsilon => exact Nat.le_refl _
  | atom => omega
  | altLeft _ ih => exact ih
  | altRight _ ih => exact ih
  | seq _ _ leftIH rightIH => exact Nat.le_trans leftIH rightIH
  | starNil => exact Nat.le_refl _
  | starCons _ _ headIH tailIH => exact Nat.le_trans headIH tailIH

/-- Boolean nullability is equivalent to denotational acceptance of every empty range. -/
theorem nullable_eq_true_iff_accepts (pattern : Regular Atom) (holdsAt : Atom → Nat → Bool)
    (position : Nat) :
    pattern.nullable = true ↔ Accepts holdsAt pattern position position := by
  induction pattern with
  | empty =>
      constructor
      · simp [nullable]
      · intro accepted
        cases accepted
  | epsilon =>
      constructor
      · intro _
        exact .epsilon position
      · intro _
        rfl
  | atom value =>
      constructor
      · simp [nullable]
      · intro accepted
        cases accepted
  | alt left right leftIH rightIH =>
      constructor
      · simp only [nullable, Bool.or_eq_true]
        intro accepted
        cases accepted with
        | inl leftAccepted => exact .altLeft (leftIH.mp leftAccepted)
        | inr rightAccepted => exact .altRight (rightIH.mp rightAccepted)
      · intro accepted
        cases accepted with
        | altLeft leftAccepted =>
            simp only [nullable, Bool.or_eq_true]
            exact Or.inl (leftIH.mpr leftAccepted)
        | altRight rightAccepted =>
            simp only [nullable, Bool.or_eq_true]
            exact Or.inr (rightIH.mpr rightAccepted)
  | seq left right leftIH rightIH =>
      constructor
      · simp only [nullable, Bool.and_eq_true]
        intro accepted
        exact .seq (leftIH.mp accepted.1) (rightIH.mp accepted.2)
      · intro accepted
        cases accepted with
        | seq leftAccepted rightAccepted =>
            rename_i middle
            have leftBound := leftAccepted.start_le_stop
            have rightBound := rightAccepted.start_le_stop
            have middleEq : middle = position := by omega
            subst middle
            simp only [nullable, Bool.and_eq_true]
            exact ⟨leftIH.mpr leftAccepted, rightIH.mpr rightAccepted⟩
  | star body bodyIH =>
      constructor
      · intro _
        exact .starNil body position
      · intro _
        rfl

/-- Push a natural number only when it is not already present. -/
@[inline] private def pushUnique (values : Array Nat) (value : Nat) : Array Nat :=
  if values.contains value then values else values.push value

/-- Append new natural numbers while retaining their first-observed order. -/
private def appendUnique (initial additions : Array Nat) : Array Nat := Id.run do
  let mut output := initial
  for value in additions do
    output := pushUnique output value
  return output

/--
Enumerate accepted stop positions at or before `stop` from one absolute start position.

The result is a finite reference semantics rather than the optimized execution engine. Star uses
a bounded graph closure over input fenceposts, so nullable bodies cannot make it diverge.
-/
def endpoints (pattern : Regular Atom) (holdsAt : Atom → Nat → Bool)
    (start stop : Nat) : Array Nat :=
  match pattern with
  | .empty => #[]
  | .epsilon => if start ≤ stop then #[start] else #[]
  | .atom value =>
      if start < stop && holdsAt value start then #[start + 1] else #[]
  | .alt left right =>
      appendUnique (endpoints left holdsAt start stop) (endpoints right holdsAt start stop)
  | .seq left right => Id.run do
      let mut output := #[]
      for middle in endpoints left holdsAt start stop do
        output := appendUnique output (endpoints right holdsAt middle stop)
      return output
  | .star body =>
      if stop < start then #[] else Id.run do
        let mut reached := #[start]
        let mut frontier := #[start]
        for _ in [0:stop - start + 1] do
          let mut next := #[]
          for position in frontier do
            for after in endpoints body holdsAt position stop do
              if !reached.contains after then
                reached := reached.push after
                next := next.push after
          frontier := next
        return reached
  termination_by pattern

/-- Decide reference acceptance of one caller-selected, normalized half-open range. -/
@[inline] def matchesRange (pattern : Regular Atom) (holdsAt : Atom → Nat → Bool)
    (size start stop : Nat) : Bool :=
  let range := normalizeRange size start stop
  (pattern.endpoints holdsAt range.start range.stop).contains range.stop

end Regular

end Nlp.Pattern
