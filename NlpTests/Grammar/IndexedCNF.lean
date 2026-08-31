import Nlp.Grammar.IndexedCNF

namespace NlpTests.Grammar.IndexedCNF

open Nlp

private def grammar : CNF Nat :=
  { bin := #[⟨0, 1, 2, 10⟩, ⟨1, 0, 1, 20⟩, ⟨2, 1, 2, 30⟩]
    lex := #[]
    start := 0
    nNT := 3 }

private def indexed := grammar.index

example : indexed.pairStart = #[0, 0, 1, 1, 1, 1, 3, 3, 3, 3] := by native_decide

example : indexed.binSorted.map (fun rule ↦ rule.lhs) = #[1, 0, 2] := by native_decide

private def withOutOfBoundsRule : CNF Nat :=
  { grammar with bin := grammar.bin.push ⟨0, 9, 0, 40⟩ }

example : withOutOfBoundsRule.index.binSorted.size = grammar.bin.size := by native_decide

end NlpTests.Grammar.IndexedCNF
