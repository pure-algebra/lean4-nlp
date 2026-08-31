import Nlp.Grammar.CNF

namespace NlpTests.Grammar.CNF

open Nlp

private def grammar : Nlp.CNF Nat :=
  { bin := #[⟨0, 1, 2, 3⟩]
    lex := #[⟨1, 10, 5⟩, ⟨2, 11, 7⟩]
    start := 0
    nNT := 3 }

example : grammar.toCFG.IsCNF := grammar.toCFG_isCNF

example : grammar.toCFG.prods.size = 3 := by native_decide

private def nonCnf : CFG Nat :=
  { prods := #[⟨0, #[.nt 1], 1⟩]
    start := 0
    nNT := 2 }

example : ¬nonCnf.IsCNF := by native_decide

end NlpTests.Grammar.CNF
