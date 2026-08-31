import Nlp.Core.Algebra.Ops
import Nlp.Grammar.CNF
import Nlp.Grammar.IndexedCNF
import Nlp.Parse.Chart

/-!
# Reference CKY parser

`ckyNaive` is deliberately the obvious `O(n³ |P|)` implementation: each split scans every
binary production.  It remains public as the correctness oracle for later indexed parsers.
-/

namespace Nlp.Parse

/-- The goal cell for a sentence of length `n`. -/
@[inline] def goalIndex (grammar : CNF K) (n : Nat) : Nat :=
  Chart.cidx n grammar.nNT 0 n grammar.start.toNat

/--
Reference semiring-generic CKY.  The result is a dense, width-major triangular chart.

Grammar identifiers are `UInt32`; conversion to `Nat` happens only at array-index boundaries.
-/
@[specialize]
def ckyNaive {K : Type} [SemiringOps K] [Inhabited K]
    (grammar : CNF K) (words : Array Tok) : Array K :=
  Id.run do
    let n := words.size
    let mut chart : Array K := Array.replicate (Chart.entryCount n grammar.nNT) 0
    for i in [0:n] do
      for rule in grammar.lex do
        if rule.tok == words[i]! then
          let target := Chart.cidx n grammar.nNT i (i + 1) rule.lhs.toNat
          chart := chart.set! target (chart[target]! + rule.w)
    for width in [2:n + 1] do
      for i in [0:n + 1 - width] do
        let j := i + width
        for split in [i + 1:j] do
          for rule in grammar.bin do
            let left := chart[Chart.cidx n grammar.nNT i split rule.r1.toNat]!
            let right := chart[Chart.cidx n grammar.nNT split j rule.r2.toNat]!
            let target := Chart.cidx n grammar.nNT i j rule.lhs.toNat
            chart := chart.set! target (chart[target]! + rule.w * left * right)
    return chart

/-- Run the reference parser and return the start-symbol value over the full sentence. -/
@[specialize]
def ckyNaiveGoal {K : Type} [SemiringOps K] [Inhabited K]
    (grammar : CNF K) (words : Array Tok) : K :=
  (ckyNaive grammar words).getD (goalIndex grammar words.size) 0

/--
Sparse CKY using nonzero-cell lists and `(r1, r2)` grammar buckets.

`BEq` is required only to ask whether a chart value equals the semiring zero.  Callers must
ensure that `value == 0` recognizes the additive identity; this is stronger than arbitrary
Boolean equality and is the only semantic use of `BEq` here.  Carriers without a sound zero test
can continue to use `ckyNaive`.
-/
@[specialize]
def ckySparse {K : Type} [SemiringOps K] [Inhabited K] [BEq K]
    (indexed : IndexedCNF K) (words : Array Tok) : Array K :=
  Id.run do
    let grammar := indexed.grammar
    let n := words.size
    let nCells := Chart.cellCount n
    let mut chart : Array K := Array.replicate (nCells * grammar.nNT) 0
    let mut nonzero : Array (Array Nat) := Array.replicate nCells #[]

    for i in [0:n] do
      let cell := Chart.tri n i (i + 1)
      let base := cell * grammar.nNT
      for rule in grammar.lex do
        if rule.tok == words[i]! && rule.lhs.toNat < grammar.nNT then
          let target := base + rule.lhs.toNat
          chart := chart.set! target (chart[target]! + rule.w)
      let mut present : Array Nat := #[]
      for nonterminal in [0:grammar.nNT] do
        if !(chart[base + nonterminal]! == 0) then
          present := present.push nonterminal
      nonzero := nonzero.set! cell present

    for width in [2:n + 1] do
      for i in [0:n + 1 - width] do
        let j := i + width
        let cell := Chart.tri n i j
        let base := cell * grammar.nNT
        for split in [i + 1:j] do
          let leftCell := Chart.tri n i split
          let rightCell := Chart.tri n split j
          let leftBase := leftCell * grammar.nNT
          let rightBase := rightCell * grammar.nNT
          for leftNt in nonzero[leftCell]! do
            let left := chart[leftBase + leftNt]!
            for rightNt in nonzero[rightCell]! do
              let right := chart[rightBase + rightNt]!
              let key := IndexedCNF.pairKey grammar.nNT leftNt rightNt
              let first := indexed.pairStart[key]!
              let stop := indexed.pairStart[key + 1]!
              for ruleIndex in [first:stop] do
                let rule := indexed.binSorted[ruleIndex]!
                let target := base + rule.lhs.toNat
                chart := chart.set! target (chart[target]! + rule.w * left * right)
        let mut present : Array Nat := #[]
        for nonterminal in [0:grammar.nNT] do
          if !(chart[base + nonterminal]! == 0) then
            present := present.push nonterminal
        nonzero := nonzero.set! cell present
    return chart

/-- Optimized CKY entry point.  Pre-index and call `ckySparse` to reuse an index across parses. -/
@[specialize]
def cky {K : Type} [SemiringOps K] [Inhabited K] [BEq K]
    (grammar : CNF K) (words : Array Tok) : Array K :=
  ckySparse grammar.index words

/-- Run optimized CKY and return the start-symbol value over the full sentence. -/
@[specialize]
def ckyGoal {K : Type} [SemiringOps K] [Inhabited K] [BEq K]
    (grammar : CNF K) (words : Array Tok) : K :=
  (cky grammar words).getD (goalIndex grammar words.size) 0

end Nlp.Parse
