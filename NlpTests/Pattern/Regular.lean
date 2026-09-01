import Nlp.Pattern.Regular

/-!
# Typed regular-pattern reference tests

These checks cover range normalization, Boolean nullability, denotational witnesses, and the
finite reference semantics, including stars with nullable bodies.
-/

namespace NlpTests.Pattern.Regular

open Nlp.Pattern

/-- Evaluate a natural-number atom against one absolute array position. -/
private def holds (input : Array Nat) (atom position : Nat) : Bool :=
  input[position]? == some atom

/-- Representative sequence and repetition patterns. -/
private def pair : Nlp.Pattern.Regular Nat :=
  .seq (.atom 1) (.atom 2)

/-- Normalization retains an in-bounds caller range exactly. -/
example : normalizeRange 5 1 4 = ⟨1, 4⟩ := by native_decide

/-- Normalization clamps an oversized stop to the full symbolic input. -/
example : normalizeRange 3 1 99 = ⟨1, 3⟩ := by native_decide

/-- An inverted range collapses at its clamped upper endpoint. -/
example : normalizeRange 5 4 2 = ⟨2, 2⟩ := by native_decide

/-- A range entirely beyond the input collapses at the input end. -/
example : normalizeRange 3 8 9 = ⟨3, 3⟩ := by native_decide

/-- Nullability follows the regular-language algebra. -/
example :
    (Nlp.Pattern.Regular.seq (.star (.atom 1)) .epsilon :
      Nlp.Pattern.Regular Nat).nullable = true := by
  native_decide

/-- A consuming sequence is not nullable. -/
example : pair.nullable = false := by native_decide

/-- The relation records the exact split point of concatenation. -/
example : Nlp.Pattern.Regular.Accepts (holds #[1, 2]) pair 0 2 := by
  exact .seq (.atom 1 0 (by native_decide)) (.atom 2 1 (by native_decide))

/-- Every denotational witness moves monotonically through the input. -/
example (accepted : Nlp.Pattern.Regular.Accepts evaluator pattern start stop) : start ≤ stop :=
  accepted.start_le_stop

/-- The proved nullability characterization supplies an empty-range witness. -/
example : Nlp.Pattern.Regular.Accepts (holds #[]) (.star (.atom 7)) 4 4 :=
  (Nlp.Pattern.Regular.nullable_eq_true_iff_accepts (.star (.atom 7)) (holds #[]) 4).mp rfl

/-- Concatenation matches only its exact two-symbol range. -/
example : pair.matchesRange (holds #[9, 1, 2, 8]) 4 1 3 = true := by native_decide
example : pair.matchesRange (holds #[9, 1, 8, 2]) 4 1 3 = false := by native_decide

/-- Alternation retains the stable first-observed endpoint order. -/
example :
    (Nlp.Pattern.Regular.alt (.atom 1) (.epsilon) : Nlp.Pattern.Regular Nat).endpoints
      (holds #[1]) 0 1 = #[1, 0] := by
  native_decide

/-- Star computes the complete bounded fencepost closure. -/
example :
    (Nlp.Pattern.Regular.star (.atom 1) : Nlp.Pattern.Regular Nat).endpoints
      (holds #[1, 1, 1]) 0 3 = #[0, 1, 2, 3] := by
  native_decide

/-- A nullable star body terminates and emits each reachable endpoint once. -/
example :
    (Nlp.Pattern.Regular.star (.alt .epsilon (.atom 1)) :
      Nlp.Pattern.Regular Nat).endpoints (holds #[1, 1]) 0 2 = #[0, 1, 2] := by
  native_decide

/-- The reference matcher uses normalized, full-column coordinates. -/
example : pair.matchesRange (holds #[0, 1, 2]) 3 1 99 = true := by native_decide
example : (.epsilon : Nlp.Pattern.Regular Nat).matchesRange (holds #[]) 0 7 3 = true := by
  native_decide

end NlpTests.Pattern.Regular
