import Nlp.Core.Algebra.Ops
import Nlp.Core.Score.Cost
import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog
import Nlp.Core.Score.Vit

/-! # Topological inside engine -/

namespace Nlp

/-- A weighted hyperedge from zero or more tail nodes to one head node. -/
structure Edge (K : Type) where
  head : UInt32
  tails : Array UInt32
  w : K
deriving Inhabited, Repr

/--
Every producer of a tail read by an edge occurs before that consuming edge.

This is the precise ordering condition needed by the single-pass engine.  It rules out cycles and
also rules out placing another contribution to a tail after that tail has already been consumed.
-/
def EdgesTopological (edges : Array (Edge K)) : Prop :=
  ∀ (consumer : Nat) (hc : consumer < edges.size) (tail : UInt32),
    tail ∈ (edges[consumer]'hc).tails →
      ∀ (producer : Nat) (hp : producer < edges.size),
        (edges[producer]'hp).head = tail → producer < consumer

/--
Compute every node's inside value in one sweep.

Precondition: `EdgesTopological edges`.  The runtime kernel intentionally does not inspect or sort
the edges; a future checked constructor or a proof module can discharge that erased proposition.
The semiring's own zero supplies all out-of-range defaults, so no `Inhabited K` or panic path is
needed.
-/
@[specialize]
def inside {K : Type} [SemiringOps K] (n : Nat) (edges : Array (Edge K)) : Array K := Id.run do
  let mut values : Array K := Array.replicate n 0
  for edge in edges do
    let mut contribution : K := edge.w
    for tail in edge.tails do
      contribution := contribution * values.getD tail.toNat 0
    let head := edge.head.toNat
    values := values.set! head (values.getD head 0 + contribution)
  return values

/-- Monomorphic recognition entry point for cross-module specialization. -/
def insideRecog (n : Nat) (edges : Array (Edge Recog)) : Array Recog := inside n edges

/-- Monomorphic counting entry point for cross-module specialization. -/
def insideCount (n : Nat) (edges : Array (Edge Count)) : Array Count := inside n edges

/-- Monomorphic min-plus entry point for cross-module specialization. -/
def insideCost (n : Nat) (edges : Array (Edge Cost)) : Array Cost := inside n edges

/-- Monomorphic Viterbi entry point for cross-module specialization. -/
def insideVit (n : Nat) (edges : Array (Edge Vit)) : Array Vit := inside n edges

end Nlp
