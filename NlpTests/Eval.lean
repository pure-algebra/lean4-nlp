import Nlp.Eval

namespace NlpTests.Eval

open Nlp Nlp.Eval

private def zeroScore : PRF := 0

example : zeroScore.precision.toBits = (0.0 : Float).toBits := by native_decide
example : zeroScore.recall.toBits = (0.0 : Float).toBits := by native_decide
example : zeroScore.f1.toBits = (0.0 : Float).toBits := by native_decide

private def normalScore : PRF := { tp := 3, fp := 1, fn := 2 }

example : Float.abs (normalScore.precision - 0.75) < 1e-12 := by native_decide
example : Float.abs (normalScore.recall - 0.6) < 1e-12 := by native_decide
example : Float.abs (normalScore.f1 - (2.0 / 3.0)) < 1e-12 := by native_decide

private def scoreA : PRF := { tp := 1, fp := 2, fn := 3 }
private def scoreB : PRF := { tp := 4, fp := 5, fn := 6 }
private def scoreC : PRF := { tp := 7, fp := 8, fn := 9 }

example : (scoreA ++ scoreB) ++ scoreC = scoreA ++ (scoreB ++ scoreC) := by
  native_decide

example : scoreA ++ scoreB = scoreB ++ scoreA := by native_decide
example : zeroScore ++ scoreA = scoreA := by native_decide

example : taggingAccuracy #["N", "V"] #["N"] = (1, 2) := by native_decide
example : taggingAccuracy #["N"] #["V", "N"] = (0, 1) := by native_decide
example : taggingAccuracy #[] #["EXTRA"] = (0, 0) := by native_decide

private def goldTree : Tree :=
  .node 0 (.node 1 (.leaf 10) #[]) #[.node 2 (.leaf 11) #[]]

private def preterminalDifference : Tree :=
  .node 0 (.node 1 (.leaf 10) #[]) #[.node 3 (.leaf 11) #[]]

private def wrongTree : Tree :=
  .node 4 (.node 1 (.leaf 10) #[]) #[.node 2 (.leaf 11) #[]]

private def flatTree : Tree :=
  .node 8 (.node 1 (.leaf 10) #[])
    #[.node 1 (.leaf 11) #[], .node 1 (.leaf 12) #[], .node 1 (.leaf 13) #[],
      .node 1 (.leaf 14) #[], .node 1 (.leaf 15) #[], .node 1 (.leaf 16) #[]]

private def bracketsFromReference : Tree → Nat → Array (Cat × Nat × Nat) × Nat
  | .leaf _, start => (#[], start + 1)
  | .node cat child children, start =>
      let (firstBrackets, afterFirst) := bracketsFromReference child start
      let (restBrackets, stop) := children.attach.foldl
        (fun (accumulator, offset) ⟨tree, _⟩ ↦
          let (next, afterTree) := bracketsFromReference tree offset
          (accumulator ++ next, afterTree))
        (#[], afterFirst)
      let descendants := firstBrackets ++ restBrackets
      let isPreterminal :=
        match child with
        | .leaf _ => children.isEmpty
        | .node _ _ _ => false
      if isPreterminal then
        (descendants, stop)
      else
        (#[(cat, start, stop)] ++ descendants, stop)

private def smallTrees : Nat → Array Tree
  | 0 => #[.leaf 0, .leaf 1]
  | depth + 1 => Id.run do
      let smaller := smallTrees depth
      let mut output := smaller
      for cat in #[0, 1] do
        for first in smaller do
          output := output.push (.node cat first #[])
          for second in smaller do
            output := output.push (.node cat first #[second])
      return output

/-- The root is a bracket; its two preterminal children are not. -/
example : brackets goldTree = #[(0, 0, 2)] := by native_decide

example : brackets flatTree = #[(8, 0, 7)] := by native_decide

-- The accumulator implementation agrees with the former concatenating definition on every
-- binary-category, binary-word tree of depth at most two.
#guard (smallTrees 2).all fun tree ↦
  bracketsFrom tree 4 == bracketsFromReference tree 4 &&
    bracketsInto tree 4 #[(9, 1, 2)] ==
      (#[(9, 1, 2)] ++ (bracketsFromReference tree 4).1,
        (bracketsFromReference tree 4).2)

example : bracketScore goldTree goldTree = { tp := 1, fp := 0, fn := 0 } := by
  native_decide

example : bracketScore goldTree preterminalDifference = { tp := 1, fp := 0, fn := 0 } := by
  native_decide

example : bracketScore goldTree wrongTree = { tp := 0, fp := 1, fn := 1 } := by
  native_decide

private def duplicateGold : Tree :=
  .node 1 (.node 1 (.node 2 (.leaf 10) #[]) #[]) #[]

private def duplicatePred : Tree :=
  .node 1 (.node 2 (.leaf 10) #[]) #[]

/-- A unary nonterminal remains even though it shares its span with its preterminal child. -/
example : brackets duplicatePred = #[(1, 0, 1)] := by native_decide

example : brackets duplicateGold = #[(1, 0, 1), (1, 0, 1)] := by native_decide

/-- Only one of the two identical gold brackets may be consumed by one prediction. -/
example : bracketScore duplicateGold duplicatePred = { tp := 1, fp := 0, fn := 1 } := by
  native_decide

private def binaryArrays : Array (Array UInt32) :=
  #[#[], #[0], #[1], #[0, 0], #[0, 1], #[1, 0], #[1, 1], #[0, 0, 0],
    #[0, 0, 1], #[0, 1, 0], #[0, 1, 1], #[1, 0, 0], #[1, 0, 1], #[1, 1, 0], #[1, 1, 1]]

-- Exhaust all multisets over two keys through length three, including every ordering and duplicate.
#guard binaryArrays.all fun gold ↦
  binaryArrays.all fun pred ↦ multisetScoreHash gold pred == multisetScore gold pred

example :
    multisetScoreHash (#[1, 1, 2] : Array UInt32) #[1, 2, 2] =
      { tp := 2, fp := 1, fn := 1 } := by
  native_decide

example : splitTag "B-WORK-OF-ART" = { mark := "B", chunkType := "WORK-OF-ART" } := by
  native_decide

example : splitTag "O" = { mark := "O", chunkType := "" } := by native_decide
example : splitTag "-X" = { mark := "", chunkType := "X" } := by native_decide

private def starts (previous current : String) : Bool :=
  startOfChunk (splitTag previous) (splitTag current)

private def ends (previous current : String) : Bool :=
  endOfChunk (splitTag previous) (splitTag current)

/-- Permissive IOB1 starts a chunk on `O → I-X`. -/
example : starts "O" "I-X" = true := by native_decide

/-- A type change between `I` tags ends one chunk and starts the next. -/
example : ends "I-X" "I-Y" && starts "I-X" "I-Y" = true := by native_decide

/-- IOB2 `I-X → B-X` is both an end and a start, even without a type change. -/
example : ends "I-X" "B-X" && starts "I-X" "B-X" = true := by native_decide

/-- IOE and bracket prefixes retain conlleval's boundary clauses. -/
example : starts "O" "E-X" && ends "E-X" "O" = true := by native_decide
example : starts "O" "[-NP" && ends "[-NP" "O" = true := by native_decide
example : starts "O" "]-NP" && ends "]-NP" "O" = true := by native_decide

example : chunks #["O", "I-NP", "I-NP", "O"] = #[(1, 3, "NP")] := by
  native_decide

example : chunks #["I-X", "I-Y"] = #[(0, 1, "X"), (1, 2, "Y")] := by
  native_decide

example : chunks #["I-X", "B-X"] = #[(0, 1, "X"), (1, 2, "X")] := by
  native_decide

/-- An open chunk is flushed at the final fencepost. -/
example : chunks #["B-X", "I-X"] = #[(0, 2, "X")] := by native_decide

example : chunks #["[-X", "O", "]-Y"] = #[(0, 1, "X"), (2, 3, "Y")] := by
  native_decide

example :
    chunks #["B-WORK-OF-ART", "I-WORK-OF-ART"] = #[(0, 2, "WORK-OF-ART")] := by
  native_decide

private def goldChunks : Array String := #["B-NP", "I-NP", "O", "B-VP"]
private def wrongChunks : Array String := #["B-NP", "I-NP", "O", "B-ADJP"]

example : chunkScore goldChunks goldChunks = { tp := 2, fp := 0, fn := 0 } := by
  native_decide

example : chunkScore goldChunks wrongChunks = { tp := 1, fp := 1, fn := 1 } := by
  native_decide

private def permissiveLabels : Array String := #["I-X", "I-Y", "O", "[-Z", "]-Z"]

example :
    (chunkScore permissiveLabels permissiveLabels).fp = 0 &&
      (chunkScore permissiveLabels permissiveLabels).fn = 0 := by
  native_decide

end NlpTests.Eval
