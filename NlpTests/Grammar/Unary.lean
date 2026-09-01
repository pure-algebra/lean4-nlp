import Nlp.Grammar.UnaryRestore

/-!
# Adversarial tests for bounded acyclic unary elimination

These tests construct every source grammar through public treebank induction. They exercise exact
positional provenance, global cycle rejection, hard resource boundaries, non-associative weight
order, shared path prefixes, and lossless restoration through a wide binarized tree.
-/

namespace NlpTests.Grammar.Unary

open Nlp Nlp.Grammar

private def interner : Interner :=
  { names := #["S", "A", "B", "C", "D", "P", "Y", "w0", "w1", "w2"] }

@[inline] private def terminal (category : Cat) (word : Word) : Tree :=
  .node category (.leaf word) #[]

@[inline] private def unary (category : Cat) (child : Tree) : Tree :=
  .node category child #[]

private def unarySource? (grammar : TreebankGrammar K) (lhs rhs : NT) : Option Nat :=
  Id.run do
    let mut result := none
    for source in [0:grammar.unary.size] do
      match grammar.unary[source]? with
      | some rule =>
        if result.isNone && rule.lhs == lhs && rule.rhs == rhs then
          result := some source
      | none => pure ()
    return result

private def lexicalSource? (grammar : TreebankGrammar K) (lhs : NT)
    (word : Word) : Option Nat :=
  Id.run do
    let mut result := none
    for source in [0:grammar.lexical.size] do
      match grammar.lexical[source]? with
      | some rule =>
        if result.isNone && rule.lhs == lhs && rule.tok == word then
          result := some source
      | none => pure ()
    return result

private def emittedBinary? (grammar : CNF K) (lhs left right : NT) : Option Nat :=
  Id.run do
    let mut result := none
    for source in [0:grammar.bin.size] do
      match grammar.bin[source]? with
      | some rule =>
        if result.isNone && rule.lhs == lhs && rule.r1 == left && rule.r2 == right then
          result := some source
      | none => pure ()
    return result

private def emittedLexical? (grammar : CNF K) (lhs : NT) (word : Word) : Option Nat :=
  Id.run do
    let mut result := none
    for source in [0:grammar.lex.size] do
      match grammar.lex[source]? with
      | some rule =>
        if result.isNone && rule.lhs == lhs && rule.tok == word then
          result := some source
      | none => pure ()
    return result

private def emittedLexicalForPath? (closed : UnaryFreeGrammar K) (lhs : NT)
    (word : Word) (sourceRules : Array Nat) : Option Nat :=
  Id.run do
    let mut result := none
    for emittedSource in [0:closed.grammar.lex.size] do
      match closed.grammar.lex[emittedSource]?,
          closed.lexicalProvenance[emittedSource]? with
      | some rule, some provenance =>
        if result.isNone && rule.lhs == lhs && rule.tok == word then
          match closed.pathSourceRules? provenance.pathOrdinal with
          | some actual =>
            if actual == sourceRules then
              result := some emittedSource
          | none => pure ()
      | _, _ => pure ()
    return result

private def pathOrdinal? (closed : UnaryFreeGrammar K) (source target : NT)
    (sourceRules : Array Nat) : Option Nat :=
  Id.run do
    let mut result := none
    for pathOrdinal in [0:closed.paths.size] do
      match closed.paths[pathOrdinal]? with
      | some path =>
        if result.isNone && path.source == source && path.target == target then
          match closed.pathSourceRules? pathOrdinal with
          | some actual =>
            if actual == sourceRules then
              result := some pathOrdinal
          | none => pure ()
      | none => pure ()
    return result

private def lexicalChoices (closed : UnaryFreeGrammar K) (lhs : NT)
    (word : Word) : Array (Array Nat × Nat) :=
  Id.run do
    let mut result := #[]
    for emittedSource in [0:closed.grammar.lex.size] do
      match closed.grammar.lex[emittedSource]?,
          closed.lexicalProvenance[emittedSource]? with
      | some rule, some provenance =>
        if rule.lhs == lhs && rule.tok == word then
          match closed.pathSourceRules? provenance.pathOrdinal with
          | some sourceRules => result := result.push (sourceRules, provenance.sourceRule)
          | none => pure ()
      | _, _ => pure ()
    return result

private def chainTree : Tree :=
  unary 0 (unary 1 (terminal 2 7))

private def chainHasEveryPath : Bool :=
  match Grammar.induce interner #[chainTree] with
  | .error _ => false
  | .ok grammar =>
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1, grammar.realNT? 2 with
      | some s, some a, some b =>
        match unarySource? grammar s a, unarySource? grammar a b,
            lexicalSource? grammar b 7 with
        | some sa, some ab, some lexical =>
          closed.paths.size == 6 && closed.pathSteps.size == 3 &&
            (pathOrdinal? closed s s #[]).isSome &&
            (pathOrdinal? closed s a #[sa]).isSome &&
            (pathOrdinal? closed s b #[sa, ab]).isSome &&
            (pathOrdinal? closed a a #[]).isSome &&
            (pathOrdinal? closed a b #[ab]).isSome &&
            (pathOrdinal? closed b b #[]).isSome &&
            lexicalChoices closed s 7 == #[(#[sa, ab], lexical)]
        | _, _, _ => false
      | _, _, _ => false

/-- A two-edge chain emits its identity, prefix, and complete positional paths exactly once. -/
example : chainHasEveryPath = true := by
  native_decide

private structure NoOpsWeight where
  value : Nat
deriving Repr, DecidableEq, Inhabited

private def preparationNeedsNoWeightAlgebra : Bool :=
  match Grammar.induce interner #[chainTree] with
  | .error _ => false
  | .ok counted =>
    let grammar := counted.mapWeights fun count ↦ NoOpsWeight.mk count.toNat
    match grammar.prepareAcyclicUnaryWith .default with
    | .error _ => false
    | .ok plan => plan.source.nNT == grammar.nNT && plan.source.unary.size == 2

/-- Structural preparation completes before requiring identity or multiplication operations. -/
example : preparationNeedsNoWeightAlgebra = true := by
  native_decide

private def diamondTrees : Array Tree :=
  #[unary 0 (unary 1 (terminal 3 7)), unary 0 (unary 2 (terminal 3 7))]

private def diamondKeepsDistinctProvenance : Bool :=
  match Grammar.induce interner diamondTrees with
  | .error _ => false
  | .ok grammar =>
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1, grammar.realNT? 2,
          grammar.realNT? 3 with
      | some s, some a, some b, some c =>
        match unarySource? grammar s a, unarySource? grammar a c,
            unarySource? grammar s b, unarySource? grammar b c,
            lexicalSource? grammar c 7 with
        | some sa, some ac, some sb, some bc, some lexical =>
          lexicalChoices closed s 7 ==
            #[(#[sa, ac], lexical), (#[sb, bc], lexical)]
        | _, _, _, _, _ => false
      | _, _, _, _ => false

/-- Equal diamond endpoints remain two alternatives with different source-edge ordinals. -/
example : diamondKeepsDistinctProvenance = true := by
  native_decide

private def diamondAlternativesRestoreDistinctChains : Bool :=
  match Grammar.induce interner diamondTrees with
  | .error _ => false
  | .ok grammar =>
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1, grammar.realNT? 2,
          grammar.realNT? 3 with
      | some s, some a, some b, some c =>
        match unarySource? grammar s a, unarySource? grammar a c,
            unarySource? grammar s b, unarySource? grammar b c with
        | some sa, some ac, some sb, some bc =>
          match emittedLexicalForPath? closed s 7 #[sa, ac],
              emittedLexicalForPath? closed s 7 #[sb, bc] with
          | some throughA, some throughB =>
            throughA != throughB &&
              (closed.restoreDense? (.lexical throughA)).bind grammar.decodeBTree? ==
                some (binarize diamondTrees[0]!) &&
              (closed.restoreDense? (.lexical throughB)).bind grammar.decodeBTree? ==
                some (binarize diamondTrees[1]!) &&
              (closed.restore? (.lexical throughA)).map binarize ==
                some (binarize diamondTrees[0]!) &&
              (closed.restore? (.lexical throughB)).map binarize ==
                some (binarize diamondTrees[1]!)
          | _, _ => false
        | _, _, _, _ => false
      | _, _, _, _ => false

/-- Equal diamond endpoints restore through their distinct intermediate unary categories. -/
example : diamondAlternativesRestoreDistinctChains = true := by
  native_decide

private def directAndUnaryTrees : Array Tree :=
  #[terminal 0 7, unary 0 (terminal 1 7)]

private def directAndUnaryShapesRemainDistinct : Bool :=
  match Grammar.induce interner directAndUnaryTrees with
  | .error _ => false
  | .ok grammar =>
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1 with
      | some s, some a =>
        match unarySource? grammar s a, lexicalSource? grammar s 7,
            lexicalSource? grammar a 7 with
        | some sa, some direct, some inherited =>
          lexicalChoices closed s 7 == #[(#[], direct), (#[sa], inherited)]
        | _, _, _ => false
      | _, _ => false

/-- A direct rule and an inherited rule with equal CNF shape are never aggregated. -/
example : directAndUnaryShapesRemainDistinct = true := by
  native_decide

private def selfLoopTree : Tree :=
  unary 0 (terminal 0 7)

private def selfLoopWitnessIsExact : Bool :=
  match Grammar.induce interner #[selfLoopTree] with
  | .error _ => false
  | .ok grammar =>
    match grammar.realNT? 0 with
    | none => false
    | some s =>
      match grammar.eliminateAcyclicUnary with
      | .error (.cycle nodes sourceRules) => nodes == #[s, s] && sourceRules == #[0]
      | _ => false

/-- A self-loop is rejected with its exact closed walk and source-rule ordinal. -/
example : selfLoopWitnessIsExact = true := by
  native_decide

private def globallyCyclicTrees : Array Tree :=
  #[.node 0 (unary 3 (terminal 4 7)) #[terminal 6 8],
    .node 0 (unary 4 (terminal 3 7)) #[terminal 6 8]]

private def unreachableCycleWitnessIsExact : Bool :=
  match Grammar.induce interner globallyCyclicTrees with
  | .error _ => false
  | .ok grammar =>
    match grammar.realNT? 0, grammar.realNT? 3, grammar.realNT? 4 with
    | some s, some c, some d =>
      grammar.unary.all (fun rule ↦ rule.lhs != s) &&
        match grammar.eliminateAcyclicUnary with
        | .error (.cycle nodes sourceRules) =>
          nodes == #[c, d, c] && sourceRules == #[0, 1]
        | _ => false
    | _, _, _ => false

/-- Cycle detection covers the whole unary graph, even when the start has no unary path to it. -/
example : unreachableCycleWitnessIsExact = true := by
  native_decide

private def chainLimits : UnaryElimConfig :=
  { maxNonterminals := 3
    maxUnaryRules := 2
    maxPaths := 6
    maxPathRuleVisits := 4
    maxPathLength := 2
    maxOutputBinaryRules := 0
    maxOutputLexicalRules := 3
    maxOutputRules := 3 }

private def binaryTree : Tree :=
  unary 0 (.node 1 (terminal 2 7) #[terminal 3 8])

private def binaryLimits : UnaryElimConfig :=
  { maxNonterminals := 4
    maxUnaryRules := 1
    maxPaths := 5
    maxPathRuleVisits := 1
    maxPathLength := 1
    maxOutputBinaryRules := 2
    maxOutputLexicalRules := 2
    maxOutputRules := 4 }

private def zeroNeededLimits : UnaryElimConfig :=
  { maxNonterminals := 1
    maxUnaryRules := 0
    maxPaths := 1
    maxPathRuleVisits := 0
    maxPathLength := 0
    maxOutputBinaryRules := 0
    maxOutputLexicalRules := 1
    maxOutputRules := 1 }

private def exactAndZeroLimitsSucceed : Bool :=
  match Grammar.induce interner #[chainTree], Grammar.induce interner #[binaryTree],
      Grammar.induce interner #[terminal 0 7] with
  | .ok chain, .ok binary, .ok direct =>
    (chain.eliminateAcyclicUnaryWith chainLimits).isOk &&
      (binary.eliminateAcyclicUnaryWith binaryLimits).isOk &&
      (direct.eliminateAcyclicUnaryWith zeroNeededLimits).isOk
  | _, _, _ => false

/-- Exact limits pass, and zero is a valid limit precisely for resources not required. -/
example : exactAndZeroLimitsSucceed = true := by
  native_decide

private def unaryError? (config : UnaryElimConfig) (grammar : TreebankGrammar Count) :
    Option UnaryElimError :=
  match grammar.eliminateAcyclicUnaryWith config with
  | .ok _ => none
  | .error error => some error

private def everyOnePastLimitIsRejected : Bool :=
  match Grammar.induce interner #[chainTree], Grammar.induce interner #[binaryTree] with
  | .ok chain, .ok binary =>
    unaryError? { chainLimits with maxNonterminals := 2 } chain ==
        some (.nonterminalBudget 3 2) &&
      unaryError? { chainLimits with maxUnaryRules := 1 } chain ==
        some (.unaryRuleBudget 2 1) &&
      unaryError? { chainLimits with maxPaths := 5 } chain ==
        some (.pathBudget 6 5) &&
      unaryError? { chainLimits with maxPathRuleVisits := 3 } chain ==
        some (.pathRuleVisitBudget 4 3) &&
      unaryError? { chainLimits with maxPathLength := 1 } chain ==
        some (.pathLengthBudget 2 1) &&
      unaryError? { binaryLimits with maxOutputBinaryRules := 1 } binary ==
        some (.outputBinaryBudget 2 1) &&
      unaryError? { chainLimits with maxOutputLexicalRules := 2 } chain ==
        some (.outputLexicalBudget 3 2) &&
      unaryError? { chainLimits with maxOutputRules := 2 } chain ==
        some (.outputRuleBudget 3 2) &&
      unaryError? { chainLimits with maxPaths := 0 } chain ==
        some (.pathBudget 3 0)
  | _, _ => false

/-- Every finite policy limit rejects the first resource unit beyond its exact boundary. -/
example : everyOnePastLimitIsRejected = true := by
  native_decide

private inductive TraceWeight where
  | identity
  | atom (value : Nat)
  | multiply (left right : TraceWeight)
deriving Repr, DecidableEq, Inhabited

private instance : One TraceWeight := ⟨.identity⟩
private instance : Mul TraceWeight := ⟨.multiply⟩

private def weightedTrees : Array Tree :=
  #[unary 0 (unary 1 (terminal 2 7)),
    unary 0 (unary 1 (terminal 2 8)),
    unary 0 (terminal 1 9)]

private def lexicalWeightForPath? (closed : UnaryFreeGrammar K) (lhs : NT)
    (word : Word) (sourceRules : Array Nat) : Option K :=
  Id.run do
    let mut result := none
    for emittedSource in [0:closed.grammar.lex.size] do
      match closed.grammar.lex[emittedSource]?,
          closed.lexicalProvenance[emittedSource]? with
      | some rule, some provenance =>
        if result.isNone && rule.lhs == lhs && rule.tok == word then
          match closed.pathSourceRules? provenance.pathOrdinal with
          | some actual =>
            if actual == sourceRules then
              result := some rule.w
          | none => pure ()
      | _, _ => pure ()
    return result

private def traceWeightsPreserveExactEvaluationOrder : Bool :=
  match Grammar.induce interner weightedTrees with
  | .error _ => false
  | .ok counted =>
    let grammar := counted.mapWeights fun count ↦ TraceWeight.atom count.toNat
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1, grammar.realNT? 2 with
      | some s, some a, some b =>
        match unarySource? grammar s a, unarySource? grammar a b with
        | some sa, some ab =>
          lexicalWeightForPath? closed s 7 #[sa, ab] ==
              some (.multiply (.multiply (.atom 3) (.atom 2)) (.atom 1)) &&
            lexicalWeightForPath? closed b 7 #[] == some (.atom 1)
        | _, _ => false
      | _, _, _ => false

/-- Unary weights associate left-to-right, while an identity path returns its base unchanged. -/
example : traceWeightsPreserveExactEvaluationOrder = true := by
  native_decide

private def branchingTrees : Array Tree :=
  #[unary 0 (unary 1 (terminal 2 7)), unary 0 (unary 1 (terminal 3 8))]

private def arenaSharesCommonPrefix : Bool :=
  match Grammar.induce interner branchingTrees with
  | .error _ => false
  | .ok grammar =>
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1, grammar.realNT? 2,
          grammar.realNT? 3 with
      | some s, some a, some b, some c =>
        match unarySource? grammar s a, unarySource? grammar a b,
            unarySource? grammar a c with
        | some sa, some ab, some ac =>
          match pathOrdinal? closed s a #[sa], pathOrdinal? closed s b #[sa, ab],
              pathOrdinal? closed s c #[sa, ac] with
          | some prefixOrdinal, some leftOrdinal, some rightOrdinal =>
            match closed.paths[prefixOrdinal]?, closed.paths[leftOrdinal]?,
                closed.paths[rightOrdinal]? with
            | some common, some left, some right =>
              match left.lastStep, right.lastStep with
              | some leftStep, some rightStep =>
                closed.paths.size == 9 && closed.pathSteps.size == 5 &&
                  closed.pathSteps[leftStep]?.map UnaryPathStep.previous ==
                    some common.lastStep &&
                  closed.pathSteps[rightStep]?.map UnaryPathStep.previous ==
                    some common.lastStep &&
                  closed.pathSourceRules? leftOrdinal == some #[sa, ab] &&
                  closed.pathSourceRules? rightOrdinal == some #[sa, ac]
              | _, _ => false
            | _, _, _ => false
          | _, _, _ => false
        | _, _, _ => false
      | _, _, _, _ => false

/-- Branching paths share their arena prefix and materialize source ordinals in source order. -/
example : arenaSharesCommonPrefix = true := by
  native_decide

private def ruleTreeGrammar : CNF Count :=
  { bin := #[⟨0, 1, 2, ⟨1⟩⟩]
    lex := #[⟨1, 7, ⟨1⟩⟩, ⟨2, 8, ⟨1⟩⟩]
    start := 0
    nNT := 3 }

private def invalidNtRuleTreeGrammar : CNF Count :=
  { ruleTreeGrammar with
    bin := ruleTreeGrammar.bin.push ⟨0, 1, 3, ⟨1⟩⟩
    lex := ruleTreeGrammar.lex.push ⟨3, 9, ⟨1⟩⟩ }

private def ruleTreeDecoderChecksEveryBoundary : Bool :=
  let lexical : CNF.RuleTree := .lexical 0
  let binary : CNF.RuleTree := .binary 0 (.lexical 0) (.lexical 1)
  let mismatched : CNF.RuleTree := .binary 0 (.lexical 1) (.lexical 0)
  match lexical.decode? ruleTreeGrammar, binary.decode? ruleTreeGrammar with
  | some decodedLexical, some decodedBinary =>
    decodedLexical.root == 1 && decodedLexical.tree.yieldWords == #[7] &&
      decodedBinary.root == 0 && decodedBinary.tree.yieldWords == #[7, 8] &&
      (lexical.toTree? ruleTreeGrammar).map Tree.yieldWords == some #[7] &&
      (binary.toTree? ruleTreeGrammar).map Tree.yieldWords == some #[7, 8] &&
      ((.lexical 2 : CNF.RuleTree).decode? ruleTreeGrammar).isNone &&
      ((.lexical 2 : CNF.RuleTree).toTree? ruleTreeGrammar).isNone &&
      ((.binary 1 (.lexical 0) (.lexical 1) : CNF.RuleTree).decode?
        ruleTreeGrammar).isNone &&
      ((.binary 1 (.lexical 0) (.lexical 1) : CNF.RuleTree).toTree?
        ruleTreeGrammar).isNone &&
      ((.lexical 2 : CNF.RuleTree).decode? invalidNtRuleTreeGrammar).isNone &&
      ((.lexical 2 : CNF.RuleTree).toTree? invalidNtRuleTreeGrammar).isNone &&
      ((.binary 1 (.lexical 0) (.lexical 1) : CNF.RuleTree).decode?
        invalidNtRuleTreeGrammar).isNone &&
      ((.binary 1 (.lexical 0) (.lexical 1) : CNF.RuleTree).toTree?
        invalidNtRuleTreeGrammar).isNone &&
      (mismatched.decode? ruleTreeGrammar).isNone &&
      (mismatched.toTree? ruleTreeGrammar).isNone
  | _, _ => false

/-- Rule-tree decoding accepts exact ordinals and rejects every malformed lookup or child root. -/
example : ruleTreeDecoderChecksEveryBoundary = true := by
  native_decide

private def wideTree : Tree :=
  unary 0 (unary 1 (.node 5 (terminal 2 7) #[terminal 3 8, terminal 4 9]))

private def wideRuleTreeRestoresExactly : Bool :=
  match Grammar.induce interner #[wideTree] with
  | .error _ => false
  | .ok grammar =>
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1, grammar.realNT? 5,
          grammar.realNT? 2, grammar.realNT? 3, grammar.realNT? 4 with
      | some s, some a, some parent, some b, some c, some d =>
        match grammar.syntheticNT? ⟨parent, c, d⟩ with
        | none => false
        | some synthetic =>
          match emittedBinary? closed.grammar s b synthetic,
              emittedBinary? closed.grammar synthetic c d,
              emittedLexical? closed.grammar b 7,
              emittedLexical? closed.grammar c 8,
              emittedLexical? closed.grammar d 9 with
          | some rootRule, some spineRule, some bRule, some cRule, some dRule =>
            let derivation : CNF.RuleTree :=
              .binary rootRule (.lexical bRule)
                (.binary spineRule (.lexical cRule) (.lexical dRule))
            match unarySource? grammar s a, unarySource? grammar a parent,
                closed.binaryProvenance[rootRule]?,
                closed.restoreDenseRooted? derivation with
            | some sa, some ap, some provenance, some restored =>
              restored.root == s &&
                closed.pathSourceRules? provenance.pathOrdinal == some #[sa, ap] &&
                grammar.decodeBTree? restored.tree == some (binarize wideTree) &&
                (closed.restore? derivation).map binarize == some (binarize wideTree) &&
                (closed.restoreDense? (.lexical closed.grammar.lex.size)).isNone &&
                (closed.restoreDense?
                  (.binary rootRule (.lexical dRule)
                    (.binary spineRule (.lexical cRule) (.lexical bRule)))).isNone
            | _, _, _, _ => false
          | _, _, _, _, _ => false
      | _, _, _, _, _, _ => false

/-- Exact rule ordinals restore a unary chain above a wide tree in dense and original spaces. -/
example : wideRuleTreeRestoresExactly = true := by
  native_decide

end NlpTests.Grammar.Unary
