import Nlp.Parse.Unary

/-!
# End-to-end Viterbi tests for unary restoration

The tests pass induced treebank grammars through unary elimination, pair indexing, sparse
Viterbi CKY, exact derivation extraction, rule-tree conversion, and provenance-aware restoration.
The duplicate-rule case checks that restoration follows the winning source ordinal rather than
the displayed CNF shape.
-/

namespace NlpTests.Parse.Unary

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

private def wideTree : Tree :=
  unary 0 (.node 5 (terminal 2 7) #[terminal 3 8, terminal 4 9])

private def wideViterbiRoundTrip : Bool :=
  match Grammar.induce interner #[wideTree] with
  | .error _ => false
  | .ok counted =>
    let grammar := counted.mapWeights fun _ ↦ (1 : Vit)
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 5, grammar.realNT? 2,
          grammar.realNT? 3, grammar.realNT? 4 with
      | some s, some parent, some b, some c, some d =>
        match grammar.syntheticNT? ⟨parent, c, d⟩ with
        | none => false
        | some synthetic =>
          match emittedBinary? closed.grammar s b synthetic,
              emittedBinary? closed.grammar synthetic c d,
              emittedLexical? closed.grammar b 7,
              emittedLexical? closed.grammar c 8,
              emittedLexical? closed.grammar d 9 with
          | some rootRule, some spineRule, some bRule, some cRule, some dRule =>
            let expected : CNF.RuleTree :=
              .binary rootRule (.lexical bRule)
                (.binary spineRule (.lexical cRule) (.lexical dRule))
            let words : Array Tok := #[7, 8, 9]
            let indexed := closed.grammar.index
            let chart := Nlp.Parse.Viterbi.ckyVit indexed words
            match Nlp.Parse.Viterbi.extractDerivation indexed words chart with
            | none => false
            | some derivation =>
              derivation.toRuleTree == expected &&
                match closed.restoreDenseViterbi? derivation,
                    closed.restoreViterbi? derivation with
                | some dense, some restored =>
                  grammar.decodeBTree? dense == some (binarize wideTree) &&
                    binarize restored == binarize wideTree
                | _, _ => false
          | _, _, _, _, _ => false
      | _, _, _, _, _ => false

/-- Indexed Viterbi keeps every emitted ordinal and restores the induced unary-wide tree. -/
example : wideViterbiRoundTrip = true := by
  native_decide

private def duplicateTrees : Array Tree :=
  #[terminal 0 7, unary 0 (terminal 1 7), unary 0 (terminal 1 7)]

private def frequencyWeight (count : Count) : Vit :=
  if count.toNat == 1 then ⟨0.3⟩ else ⟨0.9⟩

private def duplicateWinnerRestoresItsUnaryPath : Bool :=
  match Grammar.induce interner duplicateTrees with
  | .error _ => false
  | .ok counted =>
    let grammar := counted.mapWeights frequencyWeight
    match grammar.eliminateAcyclicUnary with
    | .error _ => false
    | .ok closed =>
      match grammar.realNT? 0, grammar.realNT? 1 with
      | some s, some a =>
        match unarySource? grammar s a with
        | none => false
        | some sa =>
          match emittedLexicalForPath? closed s 7 #[],
              emittedLexicalForPath? closed s 7 #[sa] with
          | some directRule, some inheritedRule =>
            let words : Array Tok := #[7]
            let indexed := closed.grammar.index
            let chart := Nlp.Parse.Viterbi.ckyVit indexed words
            match closed.grammar.lex[directRule]?, closed.grammar.lex[inheritedRule]?,
                Nlp.Parse.Viterbi.extractDerivation indexed words chart with
            | some direct, some inherited, some derivation =>
              directRule != inheritedRule && direct.lhs == inherited.lhs &&
                direct.tok == inherited.tok &&
                decide (direct.w.toFloat < inherited.w.toFloat) &&
                derivation == .lexical inheritedRule s 7 &&
                derivation.toRuleTree == .lexical inheritedRule &&
                match closed.restoreViterbi? derivation with
                | some restored => binarize restored == binarize (unary 0 (terminal 1 7))
                | none => false
            | _, _, _ => false
          | _, _ => false
      | _, _ => false

/-- Equal displayed rules restore through the higher-scoring rule's exact unary provenance. -/
example : duplicateWinnerRestoresItsUnaryPath = true := by
  native_decide

end NlpTests.Parse.Unary
