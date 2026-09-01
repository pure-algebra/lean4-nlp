import Nlp.Grammar.CompiledCNF
import Nlp.Parse.Viterbi

/-!
# Viterbi CKY over validated compiled grammars

This kernel preserves the score, tie, and extraction behavior of `ckyVit` while consuming a
reusable `CompiledCNF Vit`. Lexical initialization visits only the matching token bucket. Binary
layout dispatch happens once: dense grammars use direct pair offsets, while sparse grammars query
only the compact observed-pair map and never allocate an `nNT × nNT` table in the parser.

The returned `VitChart` remains dense in the nonterminal dimension so it is directly compatible
with the legacy chart representation. For sentence length `n` and `N` nonterminals, chart space is
`Theta(n²N)` under either compiled pair layout.
-/

namespace Nlp.Parse.Viterbi

private structure CompiledVitSeed where
  score : Array Vit
  back : Array Back
  nonzero : Array (Array Nat)

@[inline] private def activeNonterminals (score : Array Vit) (base count : Nat) : Array Nat :=
  Id.run do
    let mut present : Array Nat := #[]
    for nonterminal in [0:count] do
      if !(score[base + nonterminal]!.toFloat == 0.0) then
        present := present.push nonterminal
    return present

/-- Initialize width-one cells from only the stable bucket for each observed token. -/
private def seedCompiledLexical (compiled : CompiledCNF Vit)
    (words : Array Tok) : CompiledVitSeed := Id.run do
  let grammar := compiled.grammar
  let n := words.size
  let nCells := Chart.cellCount n
  let entries := nCells * grammar.nNT
  let mut score : Array Vit := Array.replicate entries 0
  let mut back : Array Back := Array.replicate entries default
  let mut nonzero : Array (Array Nat) := Array.replicate nCells #[]
  for i in [0:n] do
    let cell := Chart.tri n i (i + 1)
    let base := cell * grammar.nNT
    if let some range := compiled.lexicalRange? words[i]! then
      for compiledIndex in [range.first:range.stop] do
        let rule := compiled.lexicalRules[compiledIndex]!
        let source := compiled.lexicalSources[compiledIndex]!
        let target := base + rule.lhs.toNat
        if shouldReplace rule.w score[target]! 0 source back[target]! then
          score := score.set! target rule.w
          back := back.set! target ⟨UInt32.ofNat source, 0⟩
    nonzero := nonzero.set! cell (activeNonterminals score base grammar.nNT)
  return ⟨score, back, nonzero⟩

/-- Dense pair-offset kernel. The layout branch stays outside the chart loops. -/
private def ckyVitCompiledDense (compiled : CompiledCNF Vit) (starts : Array Nat)
    (words : Array Tok) : VitChart := Id.run do
  let grammar := compiled.grammar
  let n := words.size
  let seed := seedCompiledLexical compiled words
  let mut score := seed.score
  let mut back := seed.back
  let mut nonzero := seed.nonzero
  for width in [2:n + 1] do
    for i in [0:n + 1 - width] do
      let j := i + width
      let cell := Chart.tri n i j
      let base := cell * grammar.nNT
      for split in [i + 1:j] do
        if split < UInt32.size then
          let leftCell := Chart.tri n i split
          let rightCell := Chart.tri n split j
          let leftBase := leftCell * grammar.nNT
          let rightBase := rightCell * grammar.nNT
          for leftNt in nonzero[leftCell]! do
            let left := score[leftBase + leftNt]!
            for rightNt in nonzero[rightCell]! do
              let right := score[rightBase + rightNt]!
              let key := IndexedCNF.pairKey grammar.nNT leftNt rightNt
              let first := starts[key]!
              let stop := starts[key + 1]!
              for compiledIndex in [first:stop] do
                let rule := compiled.binaryRules[compiledIndex]!
                let source := compiled.binarySources[compiledIndex]!
                let target := base + rule.lhs.toNat
                let candidate := rule.w * left * right
                if shouldReplace candidate score[target]! split source back[target]! then
                  score := score.set! target candidate
                  back := back.set! target
                    ⟨UInt32.ofNat source, UInt32.ofNat split⟩
      nonzero := nonzero.set! cell (activeNonterminals score base grammar.nNT)
  return ⟨score, back⟩

/-- Sparse observed-pair kernel. Only keys present in the compact index expose rule ranges. -/
private def ckyVitCompiledSparse (compiled : CompiledCNF Vit)
    (ordinals : Std.HashMap Nat Nat) (starts : Array Nat)
    (words : Array Tok) : VitChart := Id.run do
  let grammar := compiled.grammar
  let n := words.size
  let seed := seedCompiledLexical compiled words
  let mut score := seed.score
  let mut back := seed.back
  let mut nonzero := seed.nonzero
  for width in [2:n + 1] do
    for i in [0:n + 1 - width] do
      let j := i + width
      let cell := Chart.tri n i j
      let base := cell * grammar.nNT
      for split in [i + 1:j] do
        if split < UInt32.size then
          let leftCell := Chart.tri n i split
          let rightCell := Chart.tri n split j
          let leftBase := leftCell * grammar.nNT
          let rightBase := rightCell * grammar.nNT
          for leftNt in nonzero[leftCell]! do
            let left := score[leftBase + leftNt]!
            for rightNt in nonzero[rightCell]! do
              let right := score[rightBase + rightNt]!
              let key := IndexedCNF.pairKey grammar.nNT leftNt rightNt
              if let some bucket := ordinals.get? key then
                let first := starts[bucket]!
                let stop := starts[bucket + 1]!
                for compiledIndex in [first:stop] do
                  let rule := compiled.binaryRules[compiledIndex]!
                  let source := compiled.binarySources[compiledIndex]!
                  let target := base + rule.lhs.toNat
                  let candidate := rule.w * left * right
                  if shouldReplace candidate score[target]! split source back[target]! then
                    score := score.set! target candidate
                    back := back.set! target
                      ⟨UInt32.ofNat source, UInt32.ofNat split⟩
      nonzero := nonzero.set! cell (activeNonterminals score base grammar.nNT)
  return ⟨score, back⟩

/--
Run one-best CKY over a validated reusable grammar.

Exact original `CNF` rule ordinals are written to every backpointer. On nonzero score ties, the
lower split wins, followed by the lower original source-rule ordinal, exactly as in `ckyVit`.
The canonical `Vit` input caveats documented by the legacy kernel apply unchanged.
-/
def ckyVitCompiled (compiled : CompiledCNF Vit) (words : Array Tok) : VitChart :=
  match compiled.binaryIndex with
  | .dense starts => ckyVitCompiledDense compiled starts words
  | .sparse ordinals _ starts => ckyVitCompiledSparse compiled ordinals starts words

/--
Extract an exact-source derivation from a compiled Viterbi chart.

The shared grammar-only extraction seam checks chart shape, goal identifier, every backpointer,
source rule, split, child score, and recomputed score. Empty inputs, rejected parses, and malformed
charts return `none`.
-/
def extractCompiledDerivation (compiled : CompiledCNF Vit) (words : Array Tok)
    (chart : VitChart) : Option Derivation :=
  extractGrammarDerivation compiled.grammar words chart

/-- Extract the ordinary tree view of a compiled one-best derivation. -/
def extractCompiledTree (compiled : CompiledCNF Vit) (words : Array Tok)
    (chart : VitChart) : Option Tree :=
  (extractCompiledDerivation compiled words chart).map Derivation.toTree

end Nlp.Parse.Viterbi
