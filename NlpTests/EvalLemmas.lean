import Nlp.EvalLemmas

namespace NlpTests.EvalLemmas

open Nlp Nlp.Eval

example (first second third : PRF) :
    (first ++ second) ++ third = first ++ (second ++ third) :=
  PRF.append_assoc first second third

example (left right : PRF) : left ++ right = right ++ left :=
  PRF.append_comm left right

example (score : PRF) : (0 : PRF) ++ score = score := PRF.zero_append score

example (score : PRF) : score ++ (0 : PRF) = score := PRF.append_zero score

example (score : PRF) (denominator : score.tp + score.fp = 0) :
    score.precision = 0.0 :=
  PRF.precision_eq_zero_of_denominator_eq_zero score denominator

example (score : PRF) (denominator : score.tp + score.fn = 0) :
    score.recall = 0.0 :=
  PRF.recall_eq_zero_of_denominator_eq_zero score denominator

example (tree : Tree) : (bracketScore tree tree).fp = 0 := by
  rw [bracketScore_self]

example (tree : Tree) : (bracketScore tree tree).fn = 0 := by
  rw [bracketScore_self]

example (labels : Array String) : (chunkScore labels labels).fp = 0 := by
  rw [chunkScore_self]

example (labels : Array String) : (chunkScore labels labels).fn = 0 := by
  rw [chunkScore_self]

example (cat : Cat) (word : Word) : brackets (.node cat (.leaf word) #[]) = #[] :=
  brackets_preterminal cat word

example (outer preterminal : Cat) (word : Word) :
    brackets (.node outer (.node preterminal (.leaf word) #[]) #[]) =
      #[(outer, 0, 1)] :=
  brackets_unary_preterminal outer preterminal word

end NlpTests.EvalLemmas
