import Nlp.Sequence.Hmm

/-!
# Structural contracts for hidden Markov models

These theorems cover the total public boundaries that do not depend on unproved IEEE floating-
point algebra: smoothing normalization, HMM-to-chain projection, constrained arcs, and the two
degenerate decoder cases.
-/

namespace Nlp
namespace Sequence
namespace Hmm

/-- A finite positive smoothing value is accepted unchanged. -/
@[simp] theorem checkedAddK_of_finite_pos (addK : Float)
    (finite : addK.isFinite = true) (positive : 0.0 < addK) :
    checkedAddK addK = addK := by
  simp [checkedAddK, finite, positive]

/-- A non-finite smoothing value falls back to Laplace smoothing. -/
@[simp] theorem checkedAddK_of_not_finite (addK : Float)
    (notFinite : addK.isFinite = false) : checkedAddK addK = 1.0 := by
  simp [checkedAddK, notFinite]

/-- A finite non-positive smoothing value falls back to Laplace smoothing. -/
@[simp] theorem checkedAddK_of_nonpos (addK : Float)
    (finite : addK.isFinite = true) (nonpositive : ¬0.0 < addK) :
    checkedAddK addK = 1.0 := by
  simp [checkedAddK, finite, nonpositive]

/-- Estimation records the requested dense tag count. -/
@[simp] theorem estimate_nTags (sentences : Array (Array (Tok × Nat)))
    (nTags : Nat) (addK : Float) :
    (estimate sentences nTags addK).nTags = nTags := by
  simp [estimate]

/-- Storage arrays have the dimensions promised by `nTags`. -/
def WF (model : Hmm) : Prop :=
  model.start.size = model.nTags ∧ model.trans.size = model.nTags * model.nTags ∧
    model.unk.size = model.nTags

/-- Estimation creates one start cost per requested tag. -/
@[simp] theorem estimate_start_size (sentences : Array (Array (Tok × Nat)))
    (nTags : Nat) (addK : Float) :
    (estimate sentences nTags addK).start.size = nTags := by
  simp [estimate]

/-- Estimation creates a dense row-major transition matrix. -/
@[simp] theorem estimate_trans_size (sentences : Array (Array (Tok × Nat)))
    (nTags : Nat) (addK : Float) :
    (estimate sentences nTags addK).trans.size = nTags * nTags := by
  simp [estimate]

/-- Estimation creates one unknown-word cost per requested tag. -/
@[simp] theorem estimate_unk_size (sentences : Array (Array (Tok × Nat)))
    (nTags : Nat) (addK : Float) :
    (estimate sentences nTags addK).unk.size = nTags := by
  simp [estimate]

/-- Every estimated model has dimensionally well-formed dense storage. -/
theorem estimate_wf (sentences : Array (Array (Tok × Nat)))
    (nTags : Nat) (addK : Float) : (estimate sentences nTags addK).WF := by
  simp [WF]

/-- In-range start-cost reads agree with the underlying dense array. -/
theorem startCost_eq_getElem (model : Hmm) (tag : Nat) (inBounds : tag < model.start.size) :
    model.startCost tag = model.start[tag] := by
  simp [startCost, Array.getD_eq_getD_getElem?, inBounds]

/-- Out-of-range start-cost reads are the unreachable cost. -/
theorem startCost_eq_zero (model : Hmm) (tag : Nat) (outOfBounds : model.start.size ≤ tag) :
    model.startCost tag = 0 := by
  simp [startCost, Array.getD_eq_getD_getElem?, Nat.not_lt.mpr outOfBounds]

/-- In-range transition reads agree with the underlying row-major array. -/
theorem transitionCost_eq_getElem (model : Hmm) (prior next : Nat)
    (inBounds : prior * model.nTags + next < model.trans.size) :
    model.transitionCost prior next = model.trans[prior * model.nTags + next] := by
  simp [transitionCost, Array.getD_eq_getD_getElem?, inBounds]

/-- Out-of-range transition reads are the unreachable cost. -/
theorem transitionCost_eq_zero (model : Hmm) (prior next : Nat)
    (outOfBounds : model.trans.size ≤ prior * model.nTags + next) :
    model.transitionCost prior next = 0 := by
  simp [transitionCost, Array.getD_eq_getD_getElem?, Nat.not_lt.mpr outOfBounds]

/-- Every declared start state indexes the start array of a well-formed model. -/
theorem start_index_lt_of_wf (model : Hmm) (wellFormed : model.WF)
    (tag : Nat) (inBounds : tag < model.nTags) : tag < model.start.size := by
  rw [wellFormed.1]
  exact inBounds

/-- Every declared transition indexes the dense array of a well-formed model. -/
theorem transition_index_lt_of_wf (model : Hmm) (wellFormed : model.WF)
    (prior next : Nat) (priorInBounds : prior < model.nTags)
    (nextInBounds : next < model.nTags) : prior * model.nTags + next < model.trans.size := by
  rw [wellFormed.2.1]
  calc
    prior * model.nTags + next < prior * model.nTags + model.nTags :=
      Nat.add_lt_add_left nextInBounds _
    _ = (prior + 1) * model.nTags := by simp [Nat.add_mul]
    _ ≤ model.nTags * model.nTags :=
      Nat.mul_le_mul_right model.nTags (Nat.succ_le_of_lt priorInBounds)

/-- A well-formed model reads each declared start state from dense storage. -/
theorem startCost_eq_getElem_of_wf (model : Hmm) (wellFormed : model.WF)
    (tag : Nat) (inBounds : tag < model.nTags) :
    model.startCost tag = model.start[tag]'(start_index_lt_of_wf model wellFormed tag inBounds) :=
  startCost_eq_getElem model tag (start_index_lt_of_wf model wellFormed tag inBounds)

/-- A well-formed model reads each declared transition from dense storage. -/
theorem transitionCost_eq_getElem_of_wf (model : Hmm) (wellFormed : model.WF)
    (prior next : Nat) (priorInBounds : prior < model.nTags)
    (nextInBounds : next < model.nTags) :
    model.transitionCost prior next =
      model.trans[prior * model.nTags + next]'(
        transition_index_lt_of_wf model wellFormed prior next priorInBounds nextInBounds) :=
  transitionCost_eq_getElem model prior next
    (transition_index_lt_of_wf model wellFormed prior next priorInBounds nextInBounds)

/-- Projection preserves the input length exactly. -/
@[simp] theorem toChain_len (model : Hmm) (words : Array Tok) :
    (model.toChain words).len = words.size := rfl

/-- Projection preserves the model's state count exactly. -/
@[simp] theorem toChain_nS (model : Hmm) (words : Array Tok) :
    (model.toChain words).nS = model.nTags := rfl

/-- The projected chain has no final-state penalty. -/
@[simp] theorem toChain_fin (model : Hmm) (words : Array Tok) (tag : Nat) :
    (model.toChain words).fin tag = 1 := rfl

/-- Empty input has no initial HMM path. -/
@[simp] theorem toChain_init_empty (model : Hmm) (tag : Nat) :
    (model.toChain #[]).init tag = 0 := rfl

/-- An in-range first word contributes its start and emission costs. -/
theorem toChain_init_of_getElem? (model : Hmm) (words : Array Tok) (tag : Nat) (word : Tok)
    (found : words[0]? = some word) :
    (model.toChain words).init tag = model.startCost tag * model.emissionCost tag word := by
  simp [toChain, found]

/-- An in-range word contributes its transition and emission costs. -/
theorem toChain_arc_of_getElem? (model : Hmm) (words : Array Tok) (position prior next : Nat)
    (word : Tok) (found : words[position]? = some word) :
    (model.toChain words).arc position prior next =
      model.transitionCost prior next * model.emissionCost next word := by
  simp [toChain, found]

/-- A position beyond the word array is an unreachable transition. -/
theorem toChain_arc_of_getElem?_none (model : Hmm) (words : Array Tok)
    (position prior next : Nat) (missing : words[position]? = none) :
    (model.toChain words).arc position prior next = 0 := by
  simp [toChain, missing]

private theorem foldl_fst_size {Item Value State : Type} (items : List Item)
    (step : Array Value × State → Item → Array Value × State)
    (preserves : ∀ state item, (step state item).1.size = state.1.size)
    (initial : Array Value × State) :
    (items.foldl step initial).1.size = initial.1.size := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items inductionHypothesis =>
    rw [List.foldl_cons, inductionHypothesis, preserves]

/-- Backtracing always returns exactly the requested number of positions. -/
@[simp] theorem backtrace_size (length : Nat) (backs : Array (Array Nat)) (bestTag : Nat) :
    (backtrace length backs bestTag).size = length := by
  rw [backtrace]
  rw [foldl_fst_size]
  · simp
  · intro state offset
    simp [backtraceStep]

/-- Decoding an empty observation sequence is empty for every public model value. -/
@[simp] theorem decode_empty (model : Hmm) : model.decode #[] = #[] := by
  simp [decode]

/-- A zero-state model cannot emit a tag path. -/
theorem decode_of_nTags_eq_zero (model : Hmm) (words : Array Tok)
    (zeroTags : model.nTags = 0) : model.decode words = #[] := by
  simp [decode, zeroTags]

/-- A nonempty sequence over at least one state decodes to exactly one tag per word. -/
theorem decode_size_of_nonempty (model : Hmm) (words : Array Tok)
    (nonempty : words.isEmpty = false) (positiveTags : 0 < model.nTags) :
    (model.decode words).size = words.size := by
  simp [decode, nonempty, Nat.ne_of_gt positiveTags]

/-- Decoder output size is completely characterized, including both degenerate branches. -/
theorem decode_size (model : Hmm) (words : Array Tok) :
    (model.decode words).size =
      if words.isEmpty || model.nTags == 0 then 0 else words.size := by
  by_cases emptyWords : words.isEmpty = true
  · simp [emptyWords, decode]
  · have nonempty : words.isEmpty = false := by
      cases value : words.isEmpty with
      | false => rfl
      | true => simp_all
    by_cases zeroTags : model.nTags = 0
    · simp [nonempty, zeroTags, decode]
    · have positiveTags : 0 < model.nTags := Nat.pos_of_ne_zero zeroTags
      simp [nonempty, zeroTags, decode_size_of_nonempty model words nonempty positiveTags]

end Hmm
end Sequence

namespace Chain

/-- Constraints preserve the chain's length. -/
@[simp] theorem constrain_len {K : Type u} [Zero K] (chain : Chain K)
    (legal : Nat → Nat → Bool) : (chain.constrain legal).len = chain.len := rfl

/-- Constraints preserve the chain's state count. -/
@[simp] theorem constrain_nS {K : Type u} [Zero K] (chain : Chain K)
    (legal : Nat → Nat → Bool) : (chain.constrain legal).nS = chain.nS := rfl

/-- Constraints preserve initial weights. -/
@[simp] theorem constrain_init {K : Type u} [Zero K] (chain : Chain K)
    (legal : Nat → Nat → Bool) (state : Nat) :
    (chain.constrain legal).init state = chain.init state := rfl

/-- Constraints preserve final weights. -/
@[simp] theorem constrain_fin {K : Type u} [Zero K] (chain : Chain K)
    (legal : Nat → Nat → Bool) (state : Nat) :
    (chain.constrain legal).fin state = chain.fin state := rfl

/-- Legal arcs retain their original weight. -/
theorem constrain_arc_of_true {K : Type u} [Zero K] (chain : Chain K)
    (legal : Nat → Nat → Bool) (position prior next : Nat)
    (allowed : legal prior next = true) :
    (chain.constrain legal).arc position prior next = chain.arc position prior next := by
  simp [constrain, allowed]

/-- Illegal arcs become the semiring zero. -/
theorem constrain_arc_of_false {K : Type u} [Zero K] (chain : Chain K)
    (legal : Nat → Nat → Bool) (position prior next : Nat)
    (forbidden : legal prior next = false) :
    (chain.constrain legal).arc position prior next = 0 := by
  simp [constrain, forbidden]

end Chain
end Nlp
