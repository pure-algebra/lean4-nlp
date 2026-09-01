import Nlp

/-!
# Cross-module smoke tests

These checks pin the newly completed paths at their module boundaries: bracketed text through
interning into bracket evaluation, and tagged observations through HMM decoding into accuracy.
-/

namespace NlpTests.Integration

open Nlp Nlp.Eval Nlp.IO Nlp.Sequence

private def goldTree :=
  "(S (NP (DT The) (NN cat)) (VP (VBD slept)))"

private def predictedTree :=
  "(S (NP (DT The) (NN cat)) (ADJP (VBD slept)))"

private def bracketedEvaluation : Bool :=
  match parseBracketed Interner.empty (goldTree ++ "\n" ++ predictedTree) with
  | .error _ => false
  | .ok (_, trees) =>
    match trees.toList with
    | [gold, predicted] => bracketScore gold predicted == { tp := 2, fp := 1, fn := 1 }
    | _ => false

#guard bracketedEvaluation

private def taggedTraining : Array (Array (Tok × Nat)) :=
  #[#[(10, 0), (11, 1)], #[(10, 0), (11, 1)], #[(10, 0), (10, 0)]]

private def hmmTaggingEvaluation : Bool :=
  let model := Nlp.Sequence.Hmm.estimate taggedTraining 2
  let predicted := model.decode #[10, 11] |>.map fun tag ↦ if tag == 0 then "N" else "V"
  taggingAccuracy #["N", "V"] predicted == (2, 2)

#guard hmmTaggingEvaluation

end NlpTests.Integration
