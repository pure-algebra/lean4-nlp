import Nlp.Grammar.IndexedCNFLemmas

/-! Concrete instantiations of the `IndexedCNF.ofCNF` structural lemmas, cross-checked against
brute-force evaluation of the counting sort. -/

namespace NlpTests.Grammar.IndexedCNFLemmas

open Nlp

private def grammar : CNF Nat :=
  { bin := #[⟨0, 1, 2, 10⟩, ⟨1, 0, 1, 20⟩, ⟨2, 1, 2, 30⟩]
    lex := #[]
    start := 0
    nNT := 3 }

example : grammar.index.pairStart.size = 10 := IndexedCNF.pairStart_size grammar

example : grammar.index.binSorted.size = grammar.index.pairStart.getD 9 0 :=
  IndexedCNF.binSorted_size grammar

example : grammar.index.binSource.size = grammar.index.binSorted.size :=
  IndexedCNF.binSource_size grammar

example : grammar.index.pairStart.getD 2 0 ≤ grammar.index.pairStart.getD 7 0 :=
  IndexedCNF.pairStart_monotone grammar (by decide) (by decide)

example : grammar.index.pairStart.getD 0 0 = 0 := IndexedCNF.pairStart_getD_zero grammar

example : grammar.index.pairStart.getD 4 0 ≤ grammar.index.binSorted.size :=
  IndexedCNF.pairStart_getD_le_binSorted_size grammar (by decide)

-- Degenerate grammar: no nonterminals at all; the boundary table is the single terminator.
private def empty : CNF Nat := { bin := #[], lex := #[], start := 0, nNT := 0 }

example : empty.index.pairStart.size = 1 := IndexedCNF.pairStart_size empty

-- The theorems agree with brute-force evaluation of the kernel.
example : grammar.index.pairStart.getD 9 0 = 3 := by native_decide

example : grammar.index.binSorted.size = 3 := by native_decide

end NlpTests.Grammar.IndexedCNFLemmas
