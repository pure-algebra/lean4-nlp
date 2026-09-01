import Nlp.Eval

/-!
# Laws for evaluation metrics

These proofs isolate algebraic and refinement facts from the executable evaluation kernels.
-/

namespace Nlp.Eval

@[simp] theorem safeRatio_zero (numerator : Nat) : safeRatio numerator 0 = 0.0 := rfl

namespace PRF

@[simp] theorem append_tp (left right : PRF) : (left ++ right).tp = left.tp + right.tp := rfl

@[simp] theorem append_fp (left right : PRF) : (left ++ right).fp = left.fp + right.fp := rfl

@[simp] theorem append_fn (left right : PRF) : (left ++ right).fn = left.fn + right.fn := rfl

/-- Componentwise score combination is associative. -/
theorem append_assoc (first second third : PRF) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  cases first with
  | mk firstTp firstFp firstFn =>
      cases second with
      | mk secondTp secondFp secondFn =>
          cases third with
          | mk thirdTp thirdFp thirdFn =>
              change
                PRF.mk ((firstTp + secondTp) + thirdTp)
                    ((firstFp + secondFp) + thirdFp)
                    ((firstFn + secondFn) + thirdFn) =
                  PRF.mk (firstTp + (secondTp + thirdTp))
                    (firstFp + (secondFp + thirdFp))
                    (firstFn + (secondFn + thirdFn))
              rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]

/-- Componentwise score combination is commutative. -/
theorem append_comm (left right : PRF) : left ++ right = right ++ left := by
  cases left with
  | mk leftTp leftFp leftFn =>
      cases right with
      | mk rightTp rightFp rightFn =>
          change
            PRF.mk (leftTp + rightTp) (leftFp + rightFp) (leftFn + rightFn) =
              PRF.mk (rightTp + leftTp) (rightFp + leftFp) (rightFn + leftFn)
          rw [Nat.add_comm leftTp, Nat.add_comm leftFp, Nat.add_comm leftFn]

@[simp] theorem zero_append (score : PRF) : (0 : PRF) ++ score = score := by
  cases score with
  | mk tp fp fn =>
      change PRF.mk (0 + tp) (0 + fp) (0 + fn) = PRF.mk tp fp fn
      rw [Nat.zero_add, Nat.zero_add, Nat.zero_add]

@[simp] theorem append_zero (score : PRF) : score ++ (0 : PRF) = score := by
  cases score with
  | mk tp fp fn =>
      change PRF.mk (tp + 0) (fp + 0) (fn + 0) = PRF.mk tp fp fn
      rw [Nat.add_zero, Nat.add_zero, Nat.add_zero]

/-- Precision is zero whenever its denominator is zero. -/
theorem precision_eq_zero_of_denominator_eq_zero (score : PRF)
    (denominator : score.tp + score.fp = 0) : score.precision = 0.0 := by
  simp [PRF.precision, denominator]

/-- Recall is zero whenever its denominator is zero. -/
theorem recall_eq_zero_of_denominator_eq_zero (score : PRF)
    (denominator : score.tp + score.fn = 0) : score.recall = 0.0 := by
  simp [PRF.recall, denominator]

@[simp] theorem precision_zero : (0 : PRF).precision = 0.0 := rfl

@[simp] theorem recall_zero : (0 : PRF).recall = 0.0 := rfl

@[simp] theorem f1_zero : (0 : PRF).f1 = 0.0 := rfl

end PRF

@[simp] theorem brackets_leaf (word : Word) : brackets (.leaf word) = #[] := by
  simp [brackets, bracketsFrom, bracketsInto]

/-- Exact preterminals contribute no nonterminal bracket. -/
@[simp] theorem brackets_preterminal (cat : Cat) (word : Word) :
    brackets (.node cat (.leaf word) #[]) = #[] := by
  simp [brackets, bracketsFrom, bracketsInto]

/-- A unary nonterminal above a preterminal retains its one-token bracket. -/
@[simp] theorem brackets_unary_preterminal (outer preterminal : Cat) (word : Word) :
    brackets (.node outer (.node preterminal (.leaf word) #[]) #[]) =
      #[(outer, 0, 1)] := by
  simp [brackets, bracketsFrom, bracketsInto]

/-- Identical multisets have only true positives. -/
@[simp] theorem multisetScore_self {Item : Type} [BEq Item] [LawfulBEq Item]
    [Inhabited Item] (items : Array Item) :
    multisetScore items items = { tp := items.size } := by
  simp [multisetScore]

/-- Identical hashable multisets have only true positives. -/
@[simp] theorem multisetScoreHash_self {Item : Type} [BEq Item] [LawfulBEq Item]
    [Hashable Item] (items : Array Item) :
    multisetScoreHash items items = { tp := items.size } := by
  simp [multisetScoreHash]

/-- A tree compared with itself has no bracket errors. -/
@[simp] theorem bracketScore_self (tree : Tree) :
    bracketScore tree tree = { tp := (brackets tree).size } := by
  simp [bracketScore]

/-- A label sequence compared with itself has no chunk errors. -/
@[simp] theorem chunkScore_self (labels : Array String) :
    chunkScore labels labels = { tp := (chunks labels).size } := by
  simp [chunkScore]

end Nlp.Eval
