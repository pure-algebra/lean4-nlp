import Nlp.Grammar.CompiledCNF
import Nlp.Core.Algebra.Laws
import Nlp.Parse.CKY

/-!
# CKY over validated compiled grammars

This kernel consumes `CompiledCNF` directly. Lexical initialization visits only rules for the
observed token, and binary inference visits only rules for nonzero child pairs. Validation and
index construction are paid once when the model is loaded, outside the sentence hot path.
-/

namespace Nlp.Parse

private structure CompiledSeed (K : Type) where
  chart : Array K
  nonzero : Array (Array Nat)

@[inline] private def activeNonterminals [Zero K] [Inhabited K] [BEq K]
    (chart : Array K) (base count : Nat) : Array Nat := Id.run do
  let mut present : Array Nat := #[]
  for nonterminal in [0:count] do
    if !(chart[base + nonterminal]! == 0) then
      present := present.push nonterminal
  return present

/-- Initialize width-one cells directly from stable lexical buckets. -/
private def seedLexical [SemiringOps K] [Inhabited K] [BEq K]
    (compiled : CompiledCNF K) (words : Array Tok) : CompiledSeed K := Id.run do
  let grammar := compiled.grammar
  let n := words.size
  let nCells := Chart.cellCount n
  let mut chart : Array K := Array.replicate (nCells * grammar.nNT) 0
  let mut nonzero : Array (Array Nat) := Array.replicate nCells #[]
  for i in [0:n] do
    let cell := Chart.tri n i (i + 1)
    let base := cell * grammar.nNT
    if let some bucket := compiled.lexicalOrdinals.get? words[i]! then
      let first := compiled.lexicalStarts[bucket]!
      let stop := compiled.lexicalStarts[bucket + 1]!
      for ruleIndex in [first:stop] do
        let rule := compiled.lexicalRules[ruleIndex]!
        let target := base + rule.lhs.toNat
        chart := chart.set! target (chart[target]! + rule.w)
    nonzero := nonzero.set! cell (activeNonterminals chart base grammar.nNT)
  return ⟨chart, nonzero⟩

/-- Dense pair-table kernel. Layout dispatch happens once, outside every chart loop. -/
private def ckyCompiledDense [SemiringOps K] [Inhabited K] [BEq K]
    (compiled : CompiledCNF K) (starts : Array Nat) (words : Array Tok) : Array K :=
  Id.run do
    let grammar := compiled.grammar
    let n := words.size
    let seed := seedLexical compiled words
    let mut chart := seed.chart
    let mut nonzero := seed.nonzero
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
              let first := starts[key]!
              let stop := starts[key + 1]!
              for ruleIndex in [first:stop] do
                let rule := compiled.binaryRules[ruleIndex]!
                let target := base + rule.lhs.toNat
                chart := chart.set! target (chart[target]! + rule.w * left * right)
        nonzero := nonzero.set! cell (activeNonterminals chart base grammar.nNT)
    return chart

/-- Sparse observed-pair kernel. Only present pair keys reach the compact starts table. -/
private def ckyCompiledSparse [SemiringOps K] [Inhabited K] [BEq K]
    (compiled : CompiledCNF K) (ordinals : Std.HashMap Nat Nat)
    (starts : Array Nat) (words : Array Tok) : Array K := Id.run do
  let grammar := compiled.grammar
  let n := words.size
  let seed := seedLexical compiled words
  let mut chart := seed.chart
  let mut nonzero := seed.nonzero
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
            if let some bucket := ordinals.get? key then
              let first := starts[bucket]!
              let stop := starts[bucket + 1]!
              for ruleIndex in [first:stop] do
                let rule := compiled.binaryRules[ruleIndex]!
                let target := base + rule.lhs.toNat
                chart := chart.set! target (chart[target]! + rule.w * left * right)
      nonzero := nonzero.set! cell (activeNonterminals chart base grammar.nNT)
  return chart

/--
Sparse semiring-generic CKY over a validated reusable grammar.

For sentence length `n` and `N` nonterminals, total work is
`Θ(n²N + lexical matches + Σ |active-left|·|active-right| + matched binary rules)`.
Space is `Θ(n²N + Σ |active cell|)`. The worst case remains cubic in sentence length and
quadratic in nonterminal count. `LawfulBEq` makes the sparse zero test sound; the erased
semiring laws justify pruning zero children and regrouping alternatives by child pair.
-/
@[specialize]
def ckyCompiled {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (compiled : CompiledCNF K) (words : Array Tok) : Array K :=
  match compiled.binaryIndex with
  | .dense starts => ckyCompiledDense compiled starts words
  | .sparse ordinals _ starts => ckyCompiledSparse compiled ordinals starts words

/-- Read the validated grammar's start-symbol value over the complete sentence. -/
@[specialize]
def ckyCompiledGoal {K : Type} [SemiringOps K] [LawfulSemiringMinusAssoc K]
    [Inhabited K] [BEq K] [LawfulBEq K]
    (compiled : CompiledCNF K) (words : Array Tok) : K :=
  (ckyCompiled compiled words).getD (goalIndex compiled.grammar words.size) 0

end Nlp.Parse
