import Nlp.Syntax.TreeArena

/-! # Checked preorder tree-arena tests -/

namespace NlpTests.Syntax.TreeArena

open Nlp Nlp.Syntax

/-- A small branching tree with three terminal forms and a repeated category label. -/
private def sample : NamedTree :=
  .node "S" (.node "NP" (.leaf "cats") #[])
    #[.node "VP" (.leaf "chase") #[.node "NP" (.leaf "mice") #[]]]

/-- Query a successfully compiled arena without exposing its private representation. -/
private def query (tree : NamedTree) (f : TreeArena → Bool) : Bool :=
  match TreeArena.ofNamedTree tree with
  | .ok arena => f arena
  | .error _ => false

/-- Preorder, child rows, parent links, siblings, and both interval systems are exact. -/
private def sampleLayout : Bool := query sample fun arena =>
  arena.nodeCount == 7 && arena.edgeCount == 6 && arena.leafCount == 3 &&
    arena.preorder == #[0, 1, 2, 3, 4, 5, 6] &&
    arena.label? 0 == some "S" && arena.label? 6 == some "mice" &&
    arena.kind? 0 == some .branch && arena.kind? 2 == some .leaf &&
    arena.parentAt? 0 == some none && arena.parent? 6 == some 5 &&
    arena.childrenOf? 0 == some #[1, 3] && arena.childrenOf? 3 == some #[4, 5] &&
    arena.childAt? 3 1 == some 5 && arena.childAt? 3 2 == none &&
    arena.leftSibling? 3 == some 1 && arena.rightSibling? 1 == some 3 &&
    arena.leftSibling? 1 == none && arena.rightSibling? 3 == none &&
    arena.preorderSpan? 3 == some (3, 7) && arena.yieldSpan? 3 == some (1, 3) &&
    arena.yieldForms == #["cats", "chase", "mice"] &&
    arena.leafNode? 1 == some 4 && arena.yieldForm? 2 == some "mice" &&
    arena.nodeAt? 7 == none && arena.checkSourceColumns &&
    (match arena.check with | .ok () => true | _ => false)

example : sampleLayout = true := by native_decide

/-- Equality at every exact construction cap succeeds. -/
example :
    (TreeArena.ofNamedTreeWith
      { maxNodes := 7, maxEdges := 6, maxTextBytes := 20 } sample).isOk = true := by
  native_decide

/-- One-short node, edge, and lexical-byte budgets fail at their first required entry. -/
private def oneShortBudgets : Bool :=
  let nodes := TreeArena.ofNamedTreeWith
    { maxNodes := 6, maxEdges := 6, maxTextBytes := 20 } sample
  let edges := TreeArena.ofNamedTreeWith
    { maxNodes := 7, maxEdges := 5, maxTextBytes := 20 } sample
  let text := TreeArena.ofNamedTreeWith
    { maxNodes := 7, maxEdges := 6, maxTextBytes := 19 } sample
  (match nodes with
    | .error (.nodeBudget 7 6) => true
    | _ => false) &&
  (match edges with
    | .error (.edgeBudget 6 5) => true
    | _ => false) &&
  (match text with
    | .error (.textBudget 20 19) => true
    | _ => false)

example : oneShortBudgets = true := by native_decide

/-- A very wide branch used to guard bounded, one-child-at-a-time stack scheduling. -/
private def wideTree : NamedTree :=
  .node "R" (.leaf "x") (Array.replicate 131_072 (.leaf "x"))

/-- A one-short wide build stops at the first unbudgeted node instead of stacking the fanout. -/
private def wideOneShort : Bool :=
  match TreeArena.ofNamedTreeWith
      { maxNodes := 2, maxEdges := 1, maxTextBytes := 2 } wideTree with
  | .error (.nodeBudget 3 2) => true
  | _ => false

example : wideOneShort = true := by native_decide

/-- Build a deeply nested tree iteratively so the arena constructor faces hostile depth. -/
private def deepTree (depth : Nat) : NamedTree := Id.run do
  let mut tree : NamedTree := .leaf "x"
  for _ in [0:depth] do
    tree := .node "X" tree #[]
  return tree

/-- Explicit-stack construction and iterative checking handle depth without recursive descent. -/
example : query (deepTree 4096) fun arena =>
    arena.nodeCount == 4097 && arena.edgeCount == 4096 && arena.leafCount == 1 &&
      arena.preorderSpan? 0 == some (0, 4097) && arena.yieldSpan? 0 == some (0, 1) := by
  native_decide

/-- Public root interval theorems expose the arena's two foundational spans. -/
example (arena : TreeArena) :
    arena.preorderSpan? arena.root = some (0, arena.nodeCount) :=
  arena.root_preorderSpan

example (arena : TreeArena) : arena.yieldSpan? arena.root = some (0, arena.leafCount) :=
  arena.root_yieldSpan

/-- Witnessed construction retains the original tree and its exact source terminal yield. -/
private def sourceWitness : Bool :=
  match TreeArena.buildNamedTree sample with
  | .error _ => false
  | .ok built =>
      built.arena.sourceTree == sample &&
        built.arena.sourceTree.yieldForms == sample.yieldForms &&
        built.arena.yieldForms == sample.yieldForms

example : sourceWitness = true := by native_decide

example (built : TreeArenaBuild sample) :
    checkNamedTreeYield sample built.arena.yieldForms = true :=
  TreeArenaBuild.sourceYieldChecked built

example (built : TreeArenaBuild sample) :
    built.arena.checkSourceColumns = true ∧ built.arena.sourceTree = sample :=
  TreeArenaBuild.sourceColumnsChecked built

end NlpTests.Syntax.TreeArena
