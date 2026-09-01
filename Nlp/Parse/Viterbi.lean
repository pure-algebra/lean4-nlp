import Nlp.Core.Score.Vit
import Nlp.Parse.CKY
import Nlp.Syntax.Tree

/-!
# One-best CKY derivation extraction

Viterbi values and provenance live in parallel charts.  Backpointers are operational data, not
part of a derivation-carrying semiring.  Ties are deterministic and left biased: the lower split
fencepost wins, then the lower rule index in the source `CNF.bin` array.

Extraction is total.  A fuel bound derived from the sentence length decreases at every recursive
call, while strict-CNF backpointers must also split the current span into two smaller spans.
Malformed chart sizes, rule indices, splits, scores, or rule provenance produce `none`.

Score equivalence assumes canonical probability-domain `Vit` inputs: weights are finite,
nonnegative values in `[0, 1]`, zero is `+0.0` rather than `-0.0`, and no positive derivation
underflows to zero when extraction is required.  NaNs, signed negative values, `-0.0`, and
out-of-range weights retain total operational behavior but carry no Viterbi correctness claim.
-/

namespace Nlp.Parse.Viterbi

/-- Provenance for one Viterbi chart entry. -/
structure Back where
  /-- Index into source `CNF.bin` for binary cells or `CNF.lex` for width-one cells. -/
  rule : UInt32
  /-- Absolute split fencepost.  Unused for width-one cells. -/
  split : UInt32
deriving DecidableEq, Repr, Inhabited

/-- Parallel Viterbi score and provenance charts, both indexed with `Chart.cidx`. -/
structure VitChart where
  score : Array Vit
  back : Array Back
deriving Repr, Inhabited

/--
A source-preserving one-best derivation.

Rule positions are retained even when multiple source productions have identical displayed
shapes. This is the semantic extraction form; `Tree` is its production-identity-free view.
-/
inductive Derivation where
  | lexical (source : Nat) (lhs : NT) (token : Tok)
  | binary (source : Nat) (lhs : NT) (split : Nat)
      (left right : Derivation)
deriving Repr, DecidableEq, Inhabited

namespace Derivation

/-- Erase production identity and split provenance into the ordinary constituency-tree view. -/
def toTree : Derivation → Tree
  | .lexical _ lhs token => .node lhs (.leaf token) #[]
  | .binary _ lhs _ left right => .node lhs left.toTree #[right.toTree]

end Derivation

@[inline] private def Back.precedes (candidateSplit candidateRule : Nat)
    (current : Back) : Bool :=
  decide (candidateSplit < current.split.toNat) ||
    (candidateSplit == current.split.toNat && decide (candidateRule < current.rule.toNat))

/-- Prefer a strictly larger score; on an exact nonzero tie, prefer the leftmost provenance. -/
@[inline] def shouldReplace (candidate current : Vit) (split rule : Nat)
    (back : Back) : Bool :=
  decide (current.toFloat < candidate.toFloat) ||
    (candidate.toFloat == current.toFloat && !(candidate.toFloat == 0.0) &&
      back.precedes split rule)

@[inline] private def sameRule (left right : BinRule Vit) : Bool :=
  left.lhs == right.lhs && left.r1 == right.r1 && left.r2 == right.r2 &&
    left.w.toFloat.toBits == right.w.toFloat.toBits

/-- Safely clamp one bucket to the aligned rule/source arrays of a possibly malformed index. -/
@[inline] private def bucketBounds? (indexed : IndexedCNF Vit)
    (key : Nat) : Option (Nat × Nat) := do
  let rawFirst ← indexed.pairStart[key]?
  let rawStop ← indexed.pairStart[key + 1]?
  let capacity := min indexed.binSorted.size indexed.binSource.size
  let first := min rawFirst capacity
  let stop := min rawStop capacity
  if first ≤ stop then some (first, stop) else none

/-- Length of a normalized half-open token range. -/
@[inline] def rangeLength (words : Array Tok) (start stop : Nat) : Nat :=
  let upper := min stop words.size
  upper - min start upper

/--
Run sparse, values-only Viterbi CKY over a normalized half-open token range.

The chart uses coordinates local to the selected range. Tokens are read directly from the source
array at the normalized lower bound, without allocating a slice.
-/
def ckyVitRange (indexed : IndexedCNF Vit) (words : Array Tok)
    (start stop : Nat) : VitChart := Id.run do
  let upper := min stop words.size
  let lower := min start upper
  let n := rangeLength words start stop
  let grammar := indexed.grammar
  let nCells := Chart.cellCount n
  let entries := nCells * grammar.nNT
  let mut score : Array Vit := Array.replicate entries 0
  let mut back : Array Back := Array.replicate entries default
  let mut nonzero : Array (Array Nat) := Array.replicate nCells #[]

  for i in [0:n] do
    let cell := Chart.tri n i (i + 1)
    let base := cell * grammar.nNT
    let token := words.getD (lower + i) 0
    for ruleIndex in [0:grammar.lex.size] do
      let rule := grammar.lex[ruleIndex]!
      if rule.tok == token && rule.lhs.toNat < grammar.nNT &&
          ruleIndex < UInt32.size then
        let target := base + rule.lhs.toNat
        if shouldReplace rule.w score[target]! 0 ruleIndex back[target]! then
          score := score.set! target rule.w
          back := back.set! target ⟨UInt32.ofNat ruleIndex, 0⟩
    let mut present : Array Nat := #[]
    for nonterminal in [0:grammar.nNT] do
      if !(score[base + nonterminal]!.toFloat == 0.0) then
        present := present.push nonterminal
    nonzero := nonzero.set! cell present

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
              if let some (first, bucketStop) := bucketBounds? indexed key then
                for bucketIndex in [first:bucketStop] do
                  if let some indexedRule := indexed.binSorted[bucketIndex]? then
                    if let some sourceIndex := indexed.binSource[bucketIndex]? then
                      if sourceIndex < UInt32.size then
                        if let some rule := grammar.bin[sourceIndex]? then
                          if sameRule indexedRule rule &&
                              IndexedCNF.ruleInBounds grammar.nNT rule &&
                              rule.r1.toNat == leftNt && rule.r2.toNat == rightNt then
                            let target := base + rule.lhs.toNat
                            let candidate := rule.w * left * right
                            if shouldReplace candidate score[target]! split sourceIndex
                                back[target]! then
                              score := score.set! target candidate
                              back := back.set! target
                                ⟨UInt32.ofNat sourceIndex, UInt32.ofNat split⟩
      let mut present : Array Nat := #[]
      for nonterminal in [0:grammar.nNT] do
        if !(score[base + nonterminal]!.toFloat == 0.0) then
          present := present.push nonterminal
      nonzero := nonzero.set! cell present
  return ⟨score, back⟩

/--
Sparse, values-only Viterbi CKY with a parallel argmax chart.

An index produced by `CNF.index` preserves score semantics.  Freely constructed malformed indexes
are read conservatively: invalid buckets, source mappings, and rules contribute nothing rather
than causing an out-of-bounds panic.  Bit-level agreement with `ckyNaiveGoal` is claimed only for
the canonical `Vit` domain documented in this module header.
-/
def ckyVit (indexed : IndexedCNF Vit) (words : Array Tok) : VitChart :=
  ckyVitRange indexed words 0 words.size

/-- Full-array Viterbi CKY is definitionally the normalized full-range entrypoint. -/
theorem ckyVit_eq_range (indexed : IndexedCNF Vit) (words : Array Tok) :
    ckyVit indexed words = ckyVitRange indexed words 0 words.size := rfl

private def extractRangeAux (grammar : CNF Vit) (words : Array Tok)
    (lower length : Nat) (chart : VitChart) :
    Nat → Nat → Nat → Nat → Option Derivation
  | 0, _, _, _ => none
  | fuel + 1, i, j, cat =>
      if !(i < j && j ≤ length && cat < grammar.nNT) then none
      else
        let target := Chart.cidx length grammar.nNT i j cat
        let cellScore := chart.score.getD target 0
        if cellScore.toFloat == 0.0 then none
        else
          let provenance := chart.back.getD target default
          if j == i + 1 then
            let ruleIndex := provenance.rule.toNat
            if ruleIndex < grammar.lex.size then
              let rule := grammar.lex[ruleIndex]!
              let token := words.getD (lower + i) 0
              if rule.lhs.toNat == cat && rule.tok == token &&
                  rule.w.toFloat == cellScore.toFloat then
                some (.lexical ruleIndex rule.lhs token)
              else none
            else none
          else
            let ruleIndex := provenance.rule.toNat
            let split := provenance.split.toNat
            if !(i < split && split < j) then none
            else
              match grammar.bin[ruleIndex]? with
              | none => none
              | some rule =>
                  if rule.lhs.toNat == cat &&
                      IndexedCNF.ruleInBounds grammar.nNT rule then
                    let leftIndex :=
                      Chart.cidx length grammar.nNT i split rule.r1.toNat
                    let rightIndex :=
                      Chart.cidx length grammar.nNT split j rule.r2.toNat
                    let expected :=
                      rule.w * chart.score.getD leftIndex 0 * chart.score.getD rightIndex 0
                    if !(expected.toFloat == cellScore.toFloat) then none
                    else
                      match
                          extractRangeAux grammar words lower length chart
                            fuel i split rule.r1.toNat,
                          extractRangeAux grammar words lower length chart
                            fuel split j rule.r2.toNat with
                      | some left, some right =>
                          some (.binary ruleIndex rule.lhs split left right)
                      | _, _ => none
                  else none

private def extractAux (grammar : CNF Vit) (words : Array Tok) (chart : VitChart) :
    Nat → Nat → Nat → Nat → Option Derivation :=
  extractRangeAux grammar words 0 words.size chart

/--
Extract a source-preserving derivation from a chart over a normalized half-open token range.

The chart and all returned split fenceposts use coordinates local to the selected range. Lexical
tokens are checked against the original source array at its normalized lower bound.
-/
def extractGrammarDerivationRange (grammar : CNF Vit) (words : Array Tok)
    (start stop : Nat) (chart : VitChart) : Option Derivation :=
  let upper := min stop words.size
  let lower := min start upper
  let length := rangeLength words start stop
  let expectedSize := Chart.entryCount length grammar.nNT
  if length == 0 || grammar.start.toNat ≥ grammar.nNT ||
      chart.score.size != expectedSize || chart.back.size != expectedSize then
    none
  else
    extractRangeAux grammar words lower length chart (length + 1)
      0 length grammar.start.toNat

/--
Extract a source-preserving derivation against the exact `CNF` that owns the chart ordinals.

This is the shared extraction seam for indexed and compiled Viterbi kernels. The chart shape, goal
identifier, every backpointer, source rule, split, child score, and recomputed score are checked.
Empty inputs, rejected parses, and malformed charts return `none`.
-/
def extractGrammarDerivation (grammar : CNF Vit) (words : Array Tok)
    (chart : VitChart) : Option Derivation :=
  extractGrammarDerivationRange grammar words 0 words.size chart

/-- Extract the source-preserving one-best derivation over a normalized token range. -/
def extractDerivationRange (indexed : IndexedCNF Vit) (words : Array Tok)
    (start stop : Nat) (chart : VitChart) : Option Derivation :=
  extractGrammarDerivationRange indexed.grammar words start stop chart

/--
Extract the source-preserving one-best derivation.

Returns `none` for an empty or rejected input and for every malformed chart/provenance condition.
-/
def extractDerivation (indexed : IndexedCNF Vit) (words : Array Tok)
    (chart : VitChart) : Option Derivation :=
  extractDerivationRange indexed words 0 words.size chart

/-- Extract the ordinary tree view over a normalized token range. -/
def extractTreeRange (indexed : IndexedCNF Vit) (words : Array Tok)
    (start stop : Nat) (chart : VitChart) : Option Tree :=
  (extractDerivationRange indexed words start stop chart).map Derivation.toTree

/-- Extract the ordinary tree view of the source-preserving one-best derivation. -/
def extractTree (indexed : IndexedCNF Vit) (words : Array Tok)
    (chart : VitChart) : Option Tree :=
  extractTreeRange indexed words 0 words.size chart

end Nlp.Parse.Viterbi
