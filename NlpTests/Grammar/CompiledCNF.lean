import Nlp.Grammar.CompiledCNF

namespace NlpTests.Grammar.CompiledCNF

open Nlp

private def grammar : CNF Nat :=
  { bin :=
      #[⟨0, 1, 2, 10⟩, ⟨3, 0, 1, 20⟩, ⟨2, 1, 2, 30⟩, ⟨1, 0, 1, 40⟩,
        ⟨0, 1, 2, 50⟩]
    lex := #[⟨1, 7, 11⟩, ⟨2, 8, 12⟩, ⟨3, 7, 13⟩, ⟨1, 7, 14⟩]
    start := 0
    nNT := 4 }

private def denseConfig : CompileConfig := { densePairCells := 16 }

private def sparseConfig : CompileConfig := { densePairCells := 15 }

private def error? [Inhabited K] (result : Except CompileError (CompiledCNF K)) :
    Option CompileError :=
  match result with
  | .ok _ => none
  | .error error => some error

private def capacityResult (nNT binaryRules lexicalRules : Nat) :
    Bool × Option CompileError :=
  match CompiledCNF.validateCapacities nNT binaryRules lexicalRules with
  | .ok () => (true, none)
  | .error error => (false, some error)

private def layout? [Inhabited K] (result : Except CompileError (CompiledCNF K)) :
    Option PairLayout :=
  match result with
  | .ok compiled => some compiled.pairLayout
  | .error _ => none

private def binarySources? [Inhabited K]
    (result : Except CompileError (CompiledCNF K)) (left right : NT) : Option (Array Nat) :=
  match result with
  | .error _ => none
  | .ok compiled =>
    (compiled.binaryRange? left right).map fun range ↦
      compiled.binarySources.extract range.first range.stop

private def binaryShapeWeights? [Inhabited K]
    (result : Except CompileError (CompiledCNF K)) (left right : NT) :
    Option (Array (NT × NT × NT × K)) :=
  match result with
  | .error _ => none
  | .ok compiled =>
    (compiled.binaryRange? left right).map fun range ↦
      (compiled.binaryRules.extract range.first range.stop).map fun rule ↦
        (rule.lhs, rule.r1, rule.r2, rule.w)

private def lexicalSources? [Inhabited K]
    (result : Except CompileError (CompiledCNF K)) (token : Tok) : Option (Array Nat) :=
  match result with
  | .error _ => none
  | .ok compiled =>
    (compiled.lexicalRange? token).map fun range ↦
      compiled.lexicalSources.extract range.first range.stop

private def lexicalShapeWeights? [Inhabited K]
    (result : Except CompileError (CompiledCNF K)) (token : Tok) :
    Option (Array (NT × Tok × K)) :=
  match result with
  | .error _ => none
  | .ok compiled =>
    (compiled.lexicalRange? token).map fun range ↦
      (compiled.lexicalRules.extract range.first range.stop).map fun rule ↦
        (rule.lhs, rule.tok, rule.w)

private def dense := CompiledCNF.compileWith denseConfig grammar

private def sparse := CompiledCNF.compileWith sparseConfig grammar

private def checkedSparse : Option (CompiledCNF Nat) :=
  match CompiledCNF.checkSource grammar with
  | .ok checked => some (CompiledCNF.compileCheckedWith sparseConfig checked)
  | .error _ => none

example : layout? dense = some .dense := by native_decide

example : layout? sparse = some .sparse := by native_decide

example : checkedSparse.map CompiledCNF.pairLayout = some .sparse := by native_decide

example :
    checkedSparse.bind (fun compiled ↦
      (compiled.binaryRange? 1 2).map fun range ↦
        compiled.binarySources.extract range.first range.stop) = some #[0, 2, 4] := by
  native_decide

example : denseConfig.layoutFor 4 = .dense := by
  exact CompileConfig.layoutFor_eq_dense denseConfig 4 (by decide)

example : sparseConfig.layoutFor 4 = .sparse := by
  exact CompileConfig.layoutFor_eq_sparse sparseConfig 4 (by decide)

example : CompileConfig.default.layoutFor 1024 = .dense := by native_decide

example : CompileConfig.default.layoutFor 1025 = .sparse := by native_decide

example : binarySources? dense 1 2 = some #[0, 2, 4] := by native_decide

example : binarySources? sparse 1 2 = some #[0, 2, 4] := by native_decide

example : binarySources? dense 0 1 = binarySources? sparse 0 1 := by native_decide

example :
    binaryShapeWeights? dense 1 2 =
      some #[(0, 1, 2, 10), (2, 1, 2, 30), (0, 1, 2, 50)] := by
  native_decide

example : binaryShapeWeights? dense 1 2 = binaryShapeWeights? sparse 1 2 := by
  native_decide

example : lexicalSources? dense 7 = some #[0, 2, 3] := by native_decide

example : lexicalSources? dense 7 = lexicalSources? sparse 7 := by native_decide

example :
    lexicalShapeWeights? dense 7 = some #[(1, 7, 11), (3, 7, 13), (1, 7, 14)] := by
  native_decide

example : binarySources? dense 9 0 = none := by native_decide

example : lexicalSources? dense 99 = none := by native_decide

example : capacityResult UInt32.size UInt32.size UInt32.size = (true, none) := by
  native_decide

example :
    capacityResult (UInt32.size + 1) 0 0 =
      (false, some (.nonterminalCapacity (UInt32.size + 1))) := by
  native_decide

example :
    capacityResult 1 (UInt32.size + 1) 0 =
      (false, some (.binaryRuleCapacity (UInt32.size + 1))) := by
  native_decide

example :
    capacityResult 1 0 (UInt32.size + 1) =
      (false, some (.lexicalRuleCapacity (UInt32.size + 1))) := by
  native_decide

private def badStart : CNF Nat := { grammar with start := 4 }

private def badBinaryLhs : CNF Nat :=
  { grammar with bin := #[⟨4, 1, 2, 0⟩] }

private def badBinaryRight : CNF Nat :=
  { grammar with bin := #[⟨0, 1, 4, 0⟩] }

private def badBinaryLeft : CNF Nat :=
  { grammar with bin := #[⟨0, 4, 1, 0⟩] }

private def badLexicalLhs : CNF Nat :=
  { grammar with lex := #[⟨4, 7, 0⟩] }

example : error? badStart.compile = some (.invalidStart 4 4) := by native_decide

example :
    error? badBinaryLhs.compile = some (.invalidBinaryRule 0 4 1 2 4) := by
  native_decide

example :
    error? badBinaryRight.compile = some (.invalidBinaryRule 0 0 1 4 4) := by
  native_decide

example :
    error? badBinaryLeft.compile = some (.invalidBinaryRule 0 0 4 1 4) := by
  native_decide

example :
    error? badLexicalLhs.compile = some (.invalidLexicalRule 0 4 4) := by
  native_decide

private def compiled? : Option (CompiledCNF Nat) :=
  match dense with
  | .ok compiled => some compiled
  | .error _ => none

private def entrySource? : Option Nat :=
  compiled?.bind fun compiled ↦
    (compiled.binaryRange? 1 2).bind fun range ↦
      (compiled.binaryEntry? range.first).map fun entry ↦ entry.source

example : entrySource? = some 0 := by native_decide

example :
    compiled?.bind (fun compiled ↦ compiled.binaryEntry? compiled.binaryRules.size) = none := by
  native_decide

example :
    compiled?.bind (fun compiled ↦ compiled.lexicalEntry? compiled.lexicalRules.size) = none := by
  native_decide

end NlpTests.Grammar.CompiledCNF
