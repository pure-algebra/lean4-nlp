import Nlp.Grammar.CNF

/-!
# Derived indexes for CNF grammars

`IndexedCNF` groups binary productions by their pair of right-hand-side nonterminals.  It is
derived, reusable parser data: the source `CNF` remains the serialization/specification boundary.
-/

namespace Nlp

/-- A CNF grammar together with binary rules bucketed by `(r1, r2)`. -/
structure IndexedCNF (K : Type) where
  grammar : CNF K
  binSorted : Array (BinRule K)
  /-- Bucket `key` occupies `[pairStart[key], pairStart[key + 1])` in `binSorted`. -/
  pairStart : Array Nat
deriving Inhabited

namespace IndexedCNF

/-- Row-major key for a pair of nonterminals represented as array indices. -/
@[inline] def pairKey (nNT left right : Nat) : Nat := left * nNT + right

/-- Whether all three nonterminal identifiers in a binary production are in bounds. -/
@[inline] def ruleInBounds (nNT : Nat) (rule : BinRule K) : Bool :=
  rule.lhs.toNat < nNT && rule.r1.toNat < nNT && rule.r2.toNat < nNT

/-- Build stable `(r1, r2)` buckets, omitting productions whose identifiers are out of bounds. -/
def ofCNF [Inhabited K] (grammar : CNF K) : IndexedCNF K := Id.run do
  let pairCount := grammar.nNT * grammar.nNT
  let mut counts : Array Nat := Array.replicate (pairCount + 1) 0
  for rule in grammar.bin do
    if ruleInBounds grammar.nNT rule then
      let key := pairKey grammar.nNT rule.r1.toNat rule.r2.toNat
      counts := counts.modify (key + 1) (fun count ↦ count + 1)

  let mut pairStart : Array Nat := Array.replicate (pairCount + 1) 0
  let mut total := 0
  for key in [0:pairCount + 1] do
    total := total + counts[key]!
    pairStart := pairStart.set! key total

  let mut fill := pairStart
  let mut binSorted : Array (BinRule K) := Array.replicate total default
  for rule in grammar.bin do
    if ruleInBounds grammar.nNT rule then
      let key := pairKey grammar.nNT rule.r1.toNat rule.r2.toNat
      let target := fill[key]!
      binSorted := binSorted.set! target rule
      fill := fill.set! key (target + 1)
  return ⟨grammar, binSorted, pairStart⟩

end IndexedCNF

/-- Derive the reusable pair index consumed by sparse CKY. -/
def CNF.index [Inhabited K] (grammar : CNF K) : IndexedCNF K :=
  IndexedCNF.ofCNF grammar

end Nlp
