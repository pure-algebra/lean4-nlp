import Nlp.Core.Score.Count
import Nlp.Grammar.Derivation

namespace NlpTests.Grammar.Derivation

open Nlp Nlp.FreeSorted

/-! `S → "open" A "close"`; two duplicate `A → "x"` rules remain distinct generators. -/
private def grammar : CFG Count :=
  { prods :=
      #[⟨0, #[.tm 10, .nt 1, .tm 11], ⟨2⟩⟩,
        ⟨1, #[.tm 12], ⟨3⟩⟩,
        ⟨1, #[.tm 12], ⟨5⟩⟩]
    start := 0
    nNT := 2 }

private def firstLeaf : grammar.Deriv 1 :=
  Term.op (sig := grammar.signature) (⟨1, by native_decide⟩ : grammar.RuleId) .nil

private def secondLeaf : grammar.Deriv 1 :=
  Term.op (sig := grammar.signature) (⟨2, by native_decide⟩ : grammar.RuleId) .nil

private def root (child : grammar.Deriv 1) : grammar.Deriv 0 :=
  Term.op (sig := grammar.signature) (⟨0, by native_decide⟩ : grammar.RuleId)
    (.cons child .nil)

/-- Terminal literals before and after a nonterminal child retain their source ordering. -/
example : (root firstLeaf).yield = [10, 12, 11] := by
  native_decide

/-- Positional duplicate generators have distinct weights and therefore distinct derivations. -/
example : (firstLeaf.weight.toNat, secondLeaf.weight.toNat) = (3, 5) := by
  native_decide

/-- Weight folding starts at the parent rule and multiplies child values left-associatively. -/
example : ((root secondLeaf).weight.toNat) = 10 := by
  native_decide

example : grammar.Yields 0 [10, 12, 11] := by
  exact ⟨root firstLeaf, rfl⟩

end NlpTests.Grammar.Derivation
