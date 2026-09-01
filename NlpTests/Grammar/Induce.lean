import Nlp.Grammar.Induce

namespace NlpTests.Grammar.Induce

open Nlp Nlp.Grammar

/-!
The source vocabulary deliberately interleaves words and categories. Grammar induction must retain
the word identifiers but allocate a separate dense nonterminal space for observed real and
synthetic categories.
-/
private def interner : Interner :=
  { names := #["dog", "S", "NP", "runs", "VP", "N", "V", ".", "P", "barks",
      "unused"] }

private def noun : Tree :=
  .node 2 (.node 5 (.leaf 0) #[]) #[]

private def verb (word : Word) : Tree :=
  .node 4 (.node 6 (.leaf word) #[]) #[]

private def punctuation : Tree :=
  .node 8 (.leaf 7) #[]

private def nounTerminal (word : Word) : Tree :=
  .node 5 (.leaf word) #[]

private def sentence (word : Word) : Tree :=
  .node 1 noun #[verb word, punctuation]

private def wideSentence (word : Word) : Tree :=
  .node 1 noun #[verb word, nounTerminal 0, punctuation]

private def treebank : Array Tree :=
  #[sentence 3, sentence 9]

private def wideTreebank : Array Tree :=
  #[wideSentence 3, wideSentence 9]

private def induced : Except InduceError (TreebankGrammar Count) :=
  Grammar.induce interner treebank

private def wideInduced : Except InduceError (TreebankGrammar Count) :=
  Grammar.induce interner wideTreebank

private def withGrammar (f : TreebankGrammar Count → α) : Option α :=
  match induced with
  | .ok grammar => some (f grammar)
  | .error _ => none

private def binarySummary (grammar : TreebankGrammar Count) :
    Array (Nat × Nat × Nat × Nat) :=
  grammar.binary.map fun rule ↦
    (rule.lhs.toNat, rule.r1.toNat, rule.r2.toNat, rule.w.toNat)

private def unarySummary (grammar : TreebankGrammar Count) :
    Array (Nat × Nat × Nat) :=
  grammar.unary.map fun rule ↦
    (rule.lhs.toNat, rule.rhs.toNat, rule.w.toNat)

private def lexicalSummary (grammar : TreebankGrammar Count) :
    Array (Nat × Nat × Nat) :=
  grammar.lexical.map fun rule ↦
    (rule.lhs.toNat, rule.tok.toNat, rule.w.toNat)

private def binaryCount (grammar : TreebankGrammar Count) (lhs left right : NT) : Nat :=
  grammar.binary.foldl
    (fun count rule ↦
      if rule.lhs == lhs && rule.r1 == left && rule.r2 == right then
        count + rule.w.toNat
      else
        count)
    0

private def denseMixedSymbols : Bool :=
  match induced with
  | .error _ => false
  | .ok grammar =>
      let observed := #[1, 2, 4, 5, 6, 8].all fun category ↦
        match grammar.realNT? category with
        | some nonterminal => nonterminal.toNat < grammar.nNT
        | none => false
      let wordOnly := #[0, 3, 7, 9, 10].all fun identifier ↦
        (grammar.realNT? identifier).isNone
      grammar.nNT == 7 && grammar.nNT < interner.size &&
        grammar.realNT? 1 == some grammar.start && observed && wordOnly &&
        grammar.lexical.all fun rule ↦
          rule.lhs.toNat < grammar.nNT && rule.tok.toNat < interner.size

/-- Mixed source IDs become seven dense NTs while word IDs remain source IDs. -/
example : denseMixedSymbols = true := by
  native_decide

private def sharedSuffixIsExact : Bool :=
  match induced with
  | .error _ => false
  | .ok grammar =>
      match grammar.realNT? 1, grammar.realNT? 2, grammar.realNT? 4,
          grammar.realNT? 8 with
      | some parent, some np, some vp, some punct =>
          let key : SyntheticKey := ⟨parent, vp, punct⟩
          match grammar.syntheticNT? key with
          | none => false
          | some synthetic =>
              grammar.origin? synthetic == some (.synthetic 1 key) &&
                binaryCount grammar parent np synthetic == 2 &&
                binaryCount grammar synthetic vp punct == 2 &&
                grammar.syntheticIndex.size == 1
      | _, _, _, _ => false

/-- The identical `(VP, P)` suffix in two trees is hash-consed once and counted twice. -/
example : sharedSuffixIsExact = true := by
  native_decide

private def recursiveSuffixesAreReused : Bool :=
  match wideInduced with
  | .error _ => false
  | .ok grammar =>
      match grammar.realNT? 1, grammar.realNT? 4, grammar.realNT? 5,
          grammar.realNT? 8 with
      | some parent, some vp, some nounCat, some punct =>
          let innerKey : SyntheticKey := ⟨parent, nounCat, punct⟩
          match grammar.syntheticNT? innerKey with
          | none => false
          | some inner =>
              let outerKey : SyntheticKey := ⟨parent, vp, inner⟩
              match grammar.syntheticNT? outerKey with
              | none => false
              | some outer =>
                  inner != outer && grammar.syntheticIndex.size == 2 &&
                    grammar.origin? inner == some (.synthetic 1 innerKey) &&
                    grammar.origin? outer == some (.synthetic 1 outerKey) &&
                    binaryCount grammar inner nounCat punct == 2 &&
                    binaryCount grammar outer vp inner == 2
      | _, _, _, _ => false

/-- Nested suffix generators are keyed inside-out and reused across lexical variants. -/
example : recursiveSuffixesAreReused = true := by
  native_decide

private def collisionTreebank : Array Tree :=
  #[sentence 3, .node 1 noun #[verb 9, nounTerminal 0]]

private def distinctSuffixesDoNotCollide : Bool :=
  match Grammar.induce interner collisionTreebank with
  | .error _ => false
  | .ok grammar =>
      match grammar.realNT? 1, grammar.realNT? 4, grammar.realNT? 5,
          grammar.realNT? 8 with
      | some parent, some vp, some nounCat, some punct =>
          let punctuationKey : SyntheticKey := ⟨parent, vp, punct⟩
          let nounKey : SyntheticKey := ⟨parent, vp, nounCat⟩
          match grammar.syntheticNT? punctuationKey, grammar.syntheticNT? nounKey with
          | some punctuationSuffix, some nounSuffix =>
              punctuationSuffix != nounSuffix && grammar.syntheticIndex.size == 2 &&
                grammar.origin? punctuationSuffix == some (.synthetic 1 punctuationKey) &&
                grammar.origin? nounSuffix == some (.synthetic 1 nounKey)
          | _, _ => false
      | _, _, _, _ => false

/-- Keys that differ only in the right child remain distinct. -/
example : distinctSuffixesDoNotCollide = true := by
  native_decide

private def directMatchesBinarized : Bool :=
  match Grammar.induce interner wideTreebank,
      Grammar.induceBinarized interner (wideTreebank.map binarize) with
  | .ok direct, .ok materialized =>
      direct.start == materialized.start && direct.nNT == materialized.nNT &&
        direct.origins == materialized.origins &&
        binarySummary direct == binarySummary materialized &&
        unarySummary direct == unarySummary materialized &&
        lexicalSummary direct == lexicalSummary materialized
  | _, _ => false

/-- Virtual binarization is exactly the materialized `BTree` induction. -/
example : directMatchesBinarized = true := by
  native_decide

example : withGrammar TreebankGrammar.lhsTotals = some #[2, 2, 2, 2, 2, 2, 2] := by
  native_decide

private def lexicalWeight? (grammar : TreebankGrammar Prob)
    (lhs : NT) (word : Word) : Option Prob :=
  grammar.lexical.foldl
    (fun found rule ↦ if rule.lhs == lhs && rule.tok == word then some rule.w else found)
    none

private def checkedMleIsNormalized : Bool :=
  match induced with
  | .error _ => false
  | .ok counted =>
      match counted.mle with
      | .error _ => false
      | .ok estimated =>
          match estimated.realNT? 6 with
          | none => false
          | some verbTag =>
              let canonical :=
                estimated.binary.all (fun rule ↦
                  rule.w.toFloat.isFinite && decide (0.0 < rule.w.toFloat) &&
                    decide (rule.w.toFloat ≤ 1.0)) &&
                estimated.unary.all (fun rule ↦
                  rule.w.toFloat.isFinite && decide (0.0 < rule.w.toFloat) &&
                    decide (rule.w.toFloat ≤ 1.0)) &&
                estimated.lexical.all (fun rule ↦
                  rule.w.toFloat.isFinite && decide (0.0 < rule.w.toFloat) &&
                    decide (rule.w.toFloat ≤ 1.0))
              canonical &&
                (lexicalWeight? estimated verbTag 3).map (fun weight ↦
                    weight.toFloat.toBits) == some 0.5.toBits &&
                (lexicalWeight? estimated verbTag 9).map (fun weight ↦
                    weight.toFloat.toBits) == some 0.5.toBits

example : checkedMleIsNormalized = true := by
  native_decide

private def zeroCountsAreRejected : Bool :=
  match induced with
  | .error _ => false
  | .ok counted =>
      let zeroed := counted.mapWeights fun _ ↦ (⟨0⟩ : Count)
      match zeroed.mle with
      | .error (.zeroCount .binary 0) => true
      | _ => false

example : zeroCountsAreRejected = true := by
  native_decide

private def hugeCount : Count :=
  ⟨2 ^ 2048⟩

private def nonfiniteRatiosAreRejected : Bool :=
  match induced with
  | .error _ => false
  | .ok counted =>
      let huge := counted.mapWeights fun _ ↦ hugeCount
      match huge.mle with
      | .error (.invalidProbability .binary 0 count total _) =>
          count == hugeCount.toNat && total == hugeCount.toNat
      | _ => false

example : nonfiniteRatiosAreRejected = true := by
  native_decide

private def codecRoundTrip (grammar : TreebankGrammar Count) (tree : Tree) : Bool :=
  match grammar.encodeBTree? (binarize tree) with
  | none => false
  | some encoded =>
      grammar.decodeBTree? encoded == some (binarize tree) &&
        (grammar.restoreEncodedTree? encoded).map binarize == some (binarize tree)

private def allTrainingTreesRestore : Bool :=
  match wideInduced with
  | .error _ => false
  | .ok grammar => wideTreebank.all (codecRoundTrip grammar)

example : allTrainingTreesRestore = true := by
  native_decide

private def mismatchedSyntheticChildrenAreRejected : Bool :=
  match induced with
  | .error _ => false
  | .ok grammar =>
      match grammar.realNT? 1, grammar.realNT? 4, grammar.realNT? 5,
          grammar.realNT? 8 with
      | some parent, some vp, some nounCat, some punct =>
          let key : SyntheticKey := ⟨parent, vp, punct⟩
          match grammar.syntheticNT? key with
          | none => false
          | some synthetic =>
              let malformed : Tree :=
                .node synthetic (.node nounCat (.leaf 0) #[])
                  #[.node punct (.leaf 7) #[]]
              (grammar.decodeBTree? malformed).isNone
      | _, _, _, _ => false

example : mismatchedSyntheticChildrenAreRejected = true := by
  native_decide

private def unseenSyntheticSuffixCannotEncode : Bool :=
  match induced with
  | .error _ => false
  | .ok grammar =>
      let unseen : BTree :=
        .syn 1 (.unary 4 (.unary 6 (.leaf 3))) (.unary 5 (.leaf 0))
      (grammar.encodeBTree? unseen).isNone

example : unseenSyntheticSuffixCannotEncode = true := by
  native_decide

private def error? (result : Except InduceError (TreebankGrammar Count)) :
    Option InduceError :=
  match result with
  | .ok _ => none
  | .error error => some error

example : error? (Grammar.induce interner #[]) = some .emptyTreebank := by
  native_decide

example : error? (Grammar.induce interner #[.leaf 0]) = some (.bareLeafRoot 0 0) := by
  native_decide

private def otherRoot : Tree :=
  .node 2 (.node 5 (.leaf 0) #[]) #[]

example :
    error? (Grammar.induce interner #[sentence 3, otherRoot]) =
      some (.inconsistentRoot 1 1 2) := by
  native_decide

private def badCategory : Tree :=
  .node 11 (.leaf 0) #[]

example :
    error? (Grammar.induce interner #[badCategory]) =
      some (.categoryOutOfBounds 0 11 interner.size) := by
  native_decide

private def badWord : Tree :=
  .node 1 (.leaf 11) #[]

example :
    error? (Grammar.induce interner #[badWord]) =
      some (.wordOutOfBounds 0 11 interner.size) := by
  native_decide

example :
    error? (Grammar.induceWithStart interner 11 #[sentence 3]) =
      some (.invalidStart 11 interner.size) := by
  native_decide

private def syntheticRoot : BTree :=
  .syn 1 (.unary 4 (.leaf 3)) (.unary 8 (.leaf 7))

example :
    error? (Grammar.induceBinarized interner #[syntheticRoot]) =
      some (.syntheticRoot 0 1) := by
  native_decide

private def terminalBinaryChild : BTree :=
  .bin 1 (.leaf 0) (.unary 6 (.leaf 3))

example :
    error? (Grammar.induceBinarized interner #[terminalBinaryChild]) =
      some (.terminalWhereConstituentExpected 0 0) := by
  native_decide

private def terminalSibling : Tree :=
  .node 1 (.leaf 0) #[punctuation]

example :
    error? (Grammar.induce interner #[terminalSibling]) =
      some (.terminalWhereConstituentExpected 0 0) := by
  native_decide

end NlpTests.Grammar.Induce
