import Nlp.Core.Algebra.Ops

/-! # Semiring-generic linear-chain dynamic programming -/

namespace Nlp

/--
A weighted chain of `len` positions over `nS` states.

`arc t i j` is the weight of moving from state `i` at position `t - 1` to state `j` at position
`t`, including any local potential at `t`.  A zero arc represents a forbidden transition.
-/
structure Chain (K : Type u) where
  len : Nat
  nS : Nat
  init : Nat → K
  arc : Nat → Nat → Nat → K
  fin : Nat → K

namespace Chain

/-- The shared forward recurrence for recognition, counting, Viterbi, and partition functions. -/
@[specialize]
def forward {K : Type u} [SemiringOps K] (chain : Chain K) : K := Id.run do
  let mut scores : Array K := Array.ofFn (n := chain.nS) fun state ↦ chain.init state.val
  for position in [1:chain.len] do
    let previous := scores
    scores := Array.ofFn (n := chain.nS) fun next ↦ Id.run do
      let mut total : K := 0
      for prior in [0:chain.nS] do
        total := total + previous.getD prior 0 * chain.arc position prior next.val
      return total
  let mut total : K := 0
  for state in [0:chain.nS] do
    total := total + scores.getD state 0 * chain.fin state
  return total

/--
Exponential oracle: sum the weights of every state sequence.

Each path weight is built as the load-bearing left fold
`(((init * arc₁) * arc₂) …) * fin`; no multiplication reassociation is hidden in the spec.
-/
def spec {K : Type u} [SemiringOps K] (chain : Chain K) : K :=
  let rec visit (position previous : Nat) (pathWeight : K) : K :=
    if position ≥ chain.len then
      pathWeight * chain.fin previous
    else
      (List.range chain.nS).foldl
        (fun total next ↦
          total + visit (position + 1) next (pathWeight * chain.arc position previous next))
        0
  (List.range chain.nS).foldl
    (fun total state ↦ total + visit 1 state (chain.init state)) 0

end Chain

end Nlp
