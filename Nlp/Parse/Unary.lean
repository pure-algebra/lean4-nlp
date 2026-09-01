import Nlp.Grammar.UnaryRestore
import Nlp.Parse.Viterbi

/-!
# Rule-identified unary restoration for Viterbi parses

The Viterbi extractor retains the exact emitted binary or lexical rule ordinal at every node.
This module erases only its redundant labels, tokens, and split fenceposts into `CNF.RuleTree`,
then exposes exact dense and debinarized restoration through `UnaryFreeGrammar`.
-/

namespace Nlp
namespace Parse.Viterbi

namespace Derivation

/-- Preserve emitted rule identity while erasing labels, tokens, and split fenceposts. -/
def toRuleTree : Derivation → CNF.RuleTree
  | .lexical source _ _ => .lexical source
  | .binary source _ _ left right =>
      .binary source left.toRuleTree right.toRuleTree

end Derivation
end Parse.Viterbi

namespace UnaryFreeGrammar

/-- Restore a Viterbi derivation to the source grammar's pre-closure dense tree. -/
@[inline] def restoreDenseViterbi? (closed : UnaryFreeGrammar K)
    (derivation : Parse.Viterbi.Derivation) : Option Tree :=
  closed.restoreDense? derivation.toRuleTree

/-- Restore and debinarize a Viterbi derivation to its original treebank tree. -/
@[inline] def restoreViterbi? (closed : UnaryFreeGrammar K)
    (derivation : Parse.Viterbi.Derivation) : Option Tree :=
  closed.restore? derivation.toRuleTree

end UnaryFreeGrammar
end Nlp
