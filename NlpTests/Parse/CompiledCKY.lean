import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog
import Nlp.Parse.CompiledCKY

namespace NlpTests.Parse.CompiledCKY

open Nlp Nlp.Parse

private def sentence : Array Tok := #[0, 1, 2, 3, 4]

private def countGrammar : CNF Count :=
  { bin :=
      #[⟨0, 1, 2, 1⟩, ⟨2, 4, 1, 1⟩, ⟨2, 2, 3, 1⟩, ⟨1, 1, 3, 1⟩,
        ⟨3, 5, 1, 1⟩]
    lex :=
      #[⟨1, 0, 1⟩, ⟨4, 1, 1⟩, ⟨1, 2, 1⟩, ⟨5, 3, 1⟩, ⟨1, 4, 1⟩]
    start := 0
    nNT := 6 }

private def recogGrammar : CNF Recog :=
  { bin := countGrammar.bin.map fun rule => ⟨rule.lhs, rule.r1, rule.r2, 1⟩
    lex := countGrammar.lex.map fun rule => ⟨rule.lhs, rule.tok, 1⟩
    start := countGrammar.start
    nNT := countGrammar.nNT }

private def compiledChart? {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (config : CompileConfig) (grammar : CNF K) (words : Array Tok) : Option (Array K) :=
  match CompiledCNF.compileWith config grammar with
  | .ok compiled => some (ckyCompiled compiled words)
  | .error _ => none

private def compiledGoal? {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (config : CompileConfig) (grammar : CNF K) (words : Array Tok) : Option K :=
  match CompiledCNF.compileWith config grammar with
  | .ok compiled => some (ckyCompiledGoal compiled words)
  | .error _ => none

private def dense : CompileConfig := { densePairCells := 36 }
private def sparse : CompileConfig := { densePairCells := 35 }

example : compiledChart? dense countGrammar sentence = some (ckyNaive countGrammar sentence) := by
  native_decide

example : compiledChart? sparse countGrammar sentence = some (ckyNaive countGrammar sentence) := by
  native_decide

example : compiledChart? dense countGrammar sentence =
    some (ckySparse countGrammar.index sentence) := by
  native_decide

example : compiledChart? sparse countGrammar sentence =
    some (ckySparse countGrammar.index sentence) := by
  native_decide

example : (compiledGoal? dense countGrammar sentence).map Count.toNat = some 2 := by
  native_decide

example : compiledChart? dense recogGrammar sentence = some (ckyNaive recogGrammar sentence) := by
  native_decide

example : (compiledGoal? sparse recogGrammar #[0, 99]).map Recog.toBool = some false := by
  native_decide

private def duplicateLexical : CNF Count :=
  { bin := #[]
    lex := #[⟨0, 7, 1⟩, ⟨0, 7, 1⟩]
    start := 0
    nNT := 1 }

example : (compiledGoal? dense duplicateLexical #[7]).map Count.toNat = some 2 := by
  native_decide

example : compiledChart? sparse countGrammar #[] = some (ckyNaive countGrammar #[]) := by
  native_decide

private def binaryInteractions : CNF Count :=
  { bin :=
      #[⟨0, 1, 2, 1⟩, ⟨0, 1, 2, 1⟩, ⟨0, 2, 1, 1⟩,
        ⟨3, 1, 2, 1⟩, ⟨0, 1, 1, 0⟩]
    lex := #[⟨1, 7, 1⟩, ⟨2, 7, 1⟩, ⟨1, 8, 1⟩, ⟨2, 8, 1⟩]
    start := 0
    nNT := 4 }

private def interactionsDense : CompileConfig := { densePairCells := 16 }
private def interactionsSparse : CompileConfig := { densePairCells := 15 }

example : compiledChart? interactionsDense binaryInteractions #[7, 8] =
    some (ckySparse binaryInteractions.index #[7, 8]) := by
  native_decide

example : compiledChart? interactionsSparse binaryInteractions #[7, 8] =
    some (ckySparse binaryInteractions.index #[7, 8]) := by
  native_decide

example : (compiledGoal? interactionsDense binaryInteractions #[7, 8]).map Count.toNat =
    some 3 := by
  native_decide

example : (compiledGoal? interactionsSparse binaryInteractions #[7, 8]).map Count.toNat =
    some 3 := by
  native_decide

end NlpTests.Parse.CompiledCKY
