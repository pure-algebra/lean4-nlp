import Nlp.Grammar.Unary
import Nlp.Syntax.TreeLemmas

/-!
# Exact tree restoration after unary elimination

An ordinary `Tree` forgets which emitted CNF rule produced each node. That information is
essential when equal displayed rules arise from different unary paths. `CNF.RuleTree` is the
minimal grammar-neutral tree of emitted rule ordinals. Its checked decoders recover labels and
tokens from the grammar rather than trusting redundant data in a backpointer.

Restoration first rebuilds a tree in the source grammar's dense, pre-closure nonterminal space.
Every emitted ordinal is resolved through the aligned provenance arrays, and every unary source
ordinal is checked while its node is reinserted. The existing treebank codec then validates dense
origins and synthetic right-spine keys before debinarizing the result.
-/

namespace Nlp

namespace CNF

/-- A CNF derivation shape carrying the exact source-array ordinal at every production. -/
inductive RuleTree where
  /-- A lexical node produced by `CNF.lex[source]`. -/
  | lexical (source : Nat)
  /-- A binary node produced by `CNF.bin[source]`. -/
  | binary (source : Nat) (left right : RuleTree)
deriving Repr, DecidableEq, Inhabited

/-- A checked tree paired with the dense nonterminal at its root. -/
structure RootedTree where
  root : NT
  tree : Tree
deriving Repr, Inhabited

namespace RuleTree

/--
Decode exact CNF rule ordinals into a dense tree.

Every rule ordinal and nonterminal is checked. A binary node is accepted only when the decoded
child roots equal the selected rule's right-hand side.
-/
def decode? (grammar : CNF K) : RuleTree → Option RootedTree
  | .lexical source => do
      let rule ← grammar.lex[source]?
      if rule.lhs.toNat < grammar.nNT then
        return ⟨rule.lhs, .node rule.lhs (.leaf rule.tok) #[]⟩
      else
        none
  | .binary source left right => do
      let rule ← grammar.bin[source]?
      if !(rule.lhs.toNat < grammar.nNT && rule.r1.toNat < grammar.nNT &&
          rule.r2.toNat < grammar.nNT) then
        none
      let decodedLeft ← left.decode? grammar
      let decodedRight ← right.decode? grammar
      if decodedLeft.root == rule.r1 && decodedRight.root == rule.r2 then
        return ⟨rule.lhs, .node rule.lhs decodedLeft.tree #[decodedRight.tree]⟩
      else
        none

/-- Erase exact rule identity only after validating the complete derivation against its CNF. -/
def toTree? (derivation : RuleTree) (grammar : CNF K) : Option Tree :=
  (derivation.decode? grammar).map RootedTree.tree

end RuleTree
end CNF

namespace UnaryFreeGrammar

@[inline] private def ntInBounds (count : Nat) (nonterminal : NT) : Bool :=
  nonterminal.toNat < count

/-- Follow exactly `remaining` reverse-linked path steps, inserting each inner-to-outer node. -/
private def insertPathSteps? (closed : UnaryFreeGrammar K) :
    Nat → Option Nat → CNF.RootedTree → Option CNF.RootedTree
  | 0, previous, child => if previous.isNone then some child else none
  | _ + 1, none, _ => none
  | remaining + 1, some stepOrdinal, child => do
      let step ← closed.pathSteps[stepOrdinal]?
      let rule ← closed.source.unary[step.sourceRule]?
      unless ntInBounds closed.source.nNT rule.lhs &&
          ntInBounds closed.source.nNT rule.rhs && rule.rhs == child.root do
        failure
      let wrapped : CNF.RootedTree := ⟨rule.lhs, .node rule.lhs child.tree #[]⟩
      insertPathSteps? closed remaining step.previous wrapped

private theorem insertPathSteps?_yieldWords (closed : UnaryFreeGrammar K)
    {remaining : Nat} {previous : Option Nat} {child restored : CNF.RootedTree}
    (success : insertPathSteps? closed remaining previous child = some restored) :
    restored.tree.yieldWords = child.tree.yieldWords := by
  induction remaining generalizing previous child restored with
  | zero =>
      simp [insertPathSteps?] at success
      rcases success with ⟨rfl, rfl⟩
      rfl
  | succ remaining ih =>
      cases previous with
      | none => simp [insertPathSteps?] at success
      | some stepOrdinal =>
          cases stepLookup : closed.pathSteps[stepOrdinal]? with
          | none => simp [insertPathSteps?, stepLookup] at success
          | some step =>
              cases ruleLookup : closed.source.unary[step.sourceRule]? with
              | none => simp [insertPathSteps?, stepLookup, ruleLookup] at success
              | some rule =>
                  simp only [insertPathSteps?, stepLookup, ruleLookup, Bind.bind,
                    Option.bind_some] at success
                  split at success
                  · have recursive := ih (previous := step.previous)
                      (child := ⟨rule.lhs, .node rule.lhs child.tree #[]⟩)
                      (restored := restored) success
                    simpa [Tree.yieldWords_node] using recursive
                  · contradiction

/-- Reinsert one checked outermost-to-innermost unary path above a dense source subtree. -/
private def insertPath? (closed : UnaryFreeGrammar K) (path : UnaryPath K)
    (child : CNF.RootedTree) : Option CNF.RootedTree := do
  unless ntInBounds closed.source.nNT path.source &&
      ntInBounds closed.source.nNT path.target && child.root == path.target do
    failure
  let restored ← insertPathSteps? closed path.length path.lastStep child
  if restored.root == path.source then some restored else none

private theorem insertPath?_yieldWords (closed : UnaryFreeGrammar K) (path : UnaryPath K)
    {child restored : CNF.RootedTree}
    (success : insertPath? closed path child = some restored) :
    restored.tree.yieldWords = child.tree.yieldWords := by
  simp only [insertPath?, Bind.bind] at success
  split at success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨intermediate, stepSuccess, finalSuccess⟩
    split at finalSuccess
    · have equal : intermediate = restored := Option.some.inj finalSuccess
      rw [← equal]
      exact insertPathSteps?_yieldWords closed stepSuccess
    · contradiction
  · contradiction

/--
Restore exact emitted rule ordinals to a checked tree in the source grammar's dense space.

This is the structural restoration boundary. Besides bounds and child roots, it checks both
provenance lookups, the source base rule, the selected path, the emitted/base rule shape, and every
unary edge in the path. Weights are irrelevant to tree restoration and need no equality instance.
-/
def restoreDenseRooted? (closed : UnaryFreeGrammar K) :
    CNF.RuleTree → Option CNF.RootedTree
  | .lexical emittedSource => do
      let emitted ← closed.grammar.lex[emittedSource]?
      let provenance ← closed.lexicalProvenance[emittedSource]?
      let path ← closed.paths[provenance.pathOrdinal]?
      let base ← closed.source.lexical[provenance.sourceRule]?
      unless ntInBounds closed.grammar.nNT emitted.lhs &&
          ntInBounds closed.source.nNT base.lhs && emitted.lhs == path.source &&
          path.target == base.lhs && emitted.tok == base.tok do
        failure
      insertPath? closed path
        ⟨base.lhs, .node base.lhs (.leaf base.tok) #[]⟩
  | .binary emittedSource left right => do
      let emitted ← closed.grammar.bin[emittedSource]?
      let provenance ← closed.binaryProvenance[emittedSource]?
      let path ← closed.paths[provenance.pathOrdinal]?
      let base ← closed.source.binary[provenance.sourceRule]?
      unless ntInBounds closed.grammar.nNT emitted.lhs &&
          ntInBounds closed.grammar.nNT emitted.r1 &&
          ntInBounds closed.grammar.nNT emitted.r2 &&
          ntInBounds closed.source.nNT base.lhs && ntInBounds closed.source.nNT base.r1 &&
          ntInBounds closed.source.nNT base.r2 && emitted.lhs == path.source &&
          path.target == base.lhs && emitted.r1 == base.r1 && emitted.r2 == base.r2 do
        failure
      let restoredLeft ← restoreDenseRooted? closed left
      let restoredRight ← restoreDenseRooted? closed right
      unless restoredLeft.root == emitted.r1 && restoredRight.root == emitted.r2 do
        failure
      insertPath? closed path
        ⟨base.lhs, .node base.lhs restoredLeft.tree #[restoredRight.tree]⟩

/-- Restore an exact emitted derivation to the source grammar's pre-closure dense tree. -/
def restoreDense? (closed : UnaryFreeGrammar K) (derivation : CNF.RuleTree) : Option Tree :=
  (closed.restoreDenseRooted? derivation).map CNF.RootedTree.tree

/--
Restore an exact emitted derivation, validate its dense treebank encoding, and debinarize it.
-/
def restore? (closed : UnaryFreeGrammar K) (derivation : CNF.RuleTree) : Option Tree :=
  (closed.restoreDense? derivation).bind closed.source.restoreEncodedTree?

/-- Successful exact decoding and dense restoration preserve the terminal yield. -/
theorem restoreDenseRooted?_yieldWords_of_decode? (closed : UnaryFreeGrammar K)
    (derivation : CNF.RuleTree) {restored decoded : CNF.RootedTree}
    (restoreSuccess : closed.restoreDenseRooted? derivation = some restored)
    (decodeSuccess : derivation.decode? closed.grammar = some decoded) :
    restored.tree.yieldWords = decoded.tree.yieldWords := by
  induction derivation generalizing restored decoded with
  | lexical emittedSource =>
      simp only [restoreDenseRooted?, Bind.bind] at restoreSuccess
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨emitted, emittedLookup, restoreSuccess⟩
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨provenance, _, restoreSuccess⟩
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨path, _, restoreSuccess⟩
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨base, _, restoreSuccess⟩
      split at restoreSuccess
      · rename_i valid
        simp only [Bool.and_eq_true, beq_iff_eq] at valid
        have tokenEqual : emitted.tok = base.tok := valid.2
        have restoredYield := insertPath?_yieldWords closed path restoreSuccess
        simp only [CNF.RuleTree.decode?, emittedLookup, Bind.bind, Option.bind_some]
          at decodeSuccess
        split at decodeSuccess
        · have decodedEqual :
              ⟨emitted.lhs, Tree.node emitted.lhs (.leaf emitted.tok) #[]⟩ = decoded :=
              Option.some.inj decodeSuccess
          have decodedTreeEqual := congrArg CNF.RootedTree.tree decodedEqual
          simp only at decodedTreeEqual
          rw [← decodedTreeEqual]
          simpa [Tree.yieldWords_node, Tree.yieldWords_leaf, tokenEqual]
            using restoredYield
        · contradiction
      · contradiction
  | binary emittedSource left right leftIH rightIH =>
      simp only [restoreDenseRooted?, Bind.bind] at restoreSuccess
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨emitted, emittedLookup, restoreSuccess⟩
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨provenance, _, restoreSuccess⟩
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨path, _, restoreSuccess⟩
      rcases Option.bind_eq_some_iff.mp restoreSuccess with
        ⟨base, _, restoreSuccess⟩
      split at restoreSuccess
      · rcases Option.bind_eq_some_iff.mp restoreSuccess with
          ⟨restoredLeft, leftRestore, restoreSuccess⟩
        rcases Option.bind_eq_some_iff.mp restoreSuccess with
          ⟨restoredRight, rightRestore, restoreSuccess⟩
        split at restoreSuccess
        · have restoredYield := insertPath?_yieldWords closed path restoreSuccess
          simp only [CNF.RuleTree.decode?, emittedLookup, Bind.bind, Option.bind_some]
            at decodeSuccess
          split at decodeSuccess
          · contradiction
          · rcases Option.bind_eq_some_iff.mp decodeSuccess with
              ⟨decodedLeft, leftDecode, decodeSuccess⟩
            rcases Option.bind_eq_some_iff.mp decodeSuccess with
              ⟨decodedRight, rightDecode, decodeSuccess⟩
            split at decodeSuccess
            · have leftYield := leftIH leftRestore leftDecode
              have rightYield := rightIH rightRestore rightDecode
              have decodedEqual :
                    ⟨emitted.lhs, Tree.node emitted.lhs decodedLeft.tree
                      #[decodedRight.tree]⟩ = decoded :=
                    Option.some.inj decodeSuccess
              have decodedTreeEqual := congrArg CNF.RootedTree.tree decodedEqual
              simp only at decodedTreeEqual
              rw [← decodedTreeEqual]
              simpa [Tree.yieldWords_node, leftYield, rightYield] using restoredYield
            · contradiction
        · contradiction
      · contradiction

end UnaryFreeGrammar
end Nlp
