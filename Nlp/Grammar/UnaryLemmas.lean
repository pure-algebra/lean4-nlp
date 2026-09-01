import Nlp.Grammar.UnaryRestore
import Nlp.Syntax.TreeLemmas

/-!
# Structural laws for acyclic unary elimination and restoration

The executable transform deliberately assumes only `One` and `Mul`. These lemmas preserve its
exact operational bracketing and prove structural facts without adding associativity or any other
semiring law.
-/

namespace Nlp

namespace UnaryFreeGrammar

/-- Successful dense restoration has the same terminal yield as checked CNF decoding. -/
theorem restoreDense?_yieldWords_of_decode? (closed : UnaryFreeGrammar K)
    (derivation : CNF.RuleTree) {restored : Tree} {decoded : CNF.RootedTree}
    (restoreSuccess : closed.restoreDense? derivation = some restored)
    (decodeSuccess : derivation.decode? closed.grammar = some decoded) :
    restored.yieldWords = decoded.tree.yieldWords := by
  simp only [restoreDense?, Option.map_eq_some_iff] at restoreSuccess
  rcases restoreSuccess with ⟨rooted, rootedSuccess, treeEqual⟩
  rw [← treeEqual]
  exact closed.restoreDenseRooted?_yieldWords_of_decode? derivation rootedSuccess
    decodeSuccess

/-- Successful dense restoration has the same terminal width as checked CNF decoding. -/
theorem restoreDense?_width_of_decode? (closed : UnaryFreeGrammar K)
    (derivation : CNF.RuleTree) {restored : Tree} {decoded : CNF.RootedTree}
    (restoreSuccess : closed.restoreDense? derivation = some restored)
    (decodeSuccess : derivation.decode? closed.grammar = some decoded) :
    restored.width = decoded.tree.width := by
  calc
    restored.width = restored.yieldWords.size := (Tree.yieldWords_size restored).symm
    _ = decoded.tree.yieldWords.size := congrArg Array.size
      (closed.restoreDense?_yieldWords_of_decode? derivation restoreSuccess decodeSuccess)
    _ = decoded.tree.width := Tree.yieldWords_size decoded.tree

end UnaryFreeGrammar
end Nlp
