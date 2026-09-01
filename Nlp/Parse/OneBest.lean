import Nlp.Parse.CKY
import Nlp.Syntax.Tree

/-!
# One-best derivation extraction for CKY

`ckyNaive` computes chart values; this module recovers the argmax derivation.  The design is
values plus backtrace: `ckyOneBest` mirrors `ckyNaive`'s loop structure exactly, accumulates the
same `⊕` value chart, and additionally records one `Back` entry per `(span, nonterminal)` cell
whenever a candidate strictly improves it.  `extractTree` rebuilds the tree top-down from the
backpointers.  `treeScore` semiring-sums weights for duplicate productions whose identity the tree
erases, then multiplies node scores as the spec-side gate: an extraction run is correct when the
extracted tree's score equals the chart's goal value.

Derivations are deliberately not carried inside the chart as a semiring: with derivations
attached, `⊕` loses commutativity on exact ties and `⊗` fails to distribute, so a
derivation-carrying carrier breaks the laws the engines assume.  The same obstruction rules out
k-best-as-a-semiring — truncated derivation lists with backpointers are not a semiring either —
so k-best must be the separate lazy extraction of Huang & Chiang 2005 built on top of these
one-best backpointers, and is out of scope here.

Tie policy: `better` is strict improvement, so the first candidate to reach a value is kept —
left-biased in split, then in rule order, matching `ckyNaive`'s loop order.
-/

namespace Nlp.Parse

/-- Backpointer for one `(span, nonterminal)` chart entry: how the recorded best value arose. -/
inductive Back where
  /-- No derivation recorded: the cell still holds the semiring zero. -/
  | none
  /-- Width-1 derivation by the lexical production at index `rule` in `CNF.lex`. -/
  | lex (rule : UInt32)
  /-- Binary derivation by the production at index `rule` in `CNF.bin`, splitting the span at
  absolute fencepost `split`. -/
  | bin (rule : UInt32) (split : UInt32)
deriving Repr, Inhabited, BEq

/--
Viterbi CKY with backpointers: `ckyNaive`'s loop structure verbatim, plus a `Back` array indexed
exactly like the value chart (`Chart.cidx`).

The value chart is accumulated with `⊕` in `ckyNaive`'s order, so the first component always
equals `ckyNaive grammar words` — the oracle equation the tests assert.  The backpointer of a
cell is rewritten whenever `better candidate current` holds, so `better` must decide *strict*
improvement.  For the recorded derivation to attain the cell's value, `⊕` must be selective and
`better` must decide the selection: `better a b = true → b ⊕ a = a` and
`better a b = false → b ⊕ a = b`.  This holds for `NatCost` with `<` on finite costs and for
`Vit` with `Float` strict `>`.  On ties `better` is false, so the earliest candidate is kept.
-/
@[specialize]
def ckyOneBest {K : Type} [SemiringOps K] [Inhabited K]
    (better : K → K → Bool) (grammar : CNF K) (words : Array Tok) : Array K × Array Back :=
  Id.run do
    let n := words.size
    let entries := Chart.entryCount n grammar.nNT
    let mut chart : Array K := Array.replicate entries 0
    let mut back : Array Back := Array.replicate entries .none
    for i in [0:n] do
      for ruleIdx in [0:grammar.lex.size] do
        let rule := grammar.lex[ruleIdx]!
        if rule.tok == words[i]! && rule.lhs.toNat < grammar.nNT then
          let target := Chart.cidx n grammar.nNT i (i + 1) rule.lhs.toNat
          let current := chart[target]!
          if better rule.w current then
            back := back.set! target (.lex (UInt32.ofNat ruleIdx))
          chart := chart.set! target (current + rule.w)
    for width in [2:n + 1] do
      for i in [0:n + 1 - width] do
        let j := i + width
        for split in [i + 1:j] do
          for ruleIdx in [0:grammar.bin.size] do
            let rule := grammar.bin[ruleIdx]!
            if IndexedCNF.ruleInBounds grammar.nNT rule then
              let left := chart[Chart.cidx n grammar.nNT i split rule.r1.toNat]!
              let right := chart[Chart.cidx n grammar.nNT split j rule.r2.toNat]!
              let target := Chart.cidx n grammar.nNT i j rule.lhs.toNat
              let candidate := rule.w * left * right
              let current := chart[target]!
              if better candidate current then
                back := back.set! target (.bin (UInt32.ofNat ruleIdx) (UInt32.ofNat split))
              chart := chart.set! target (current + candidate)
    return (chart, back)

/--
Fuel-indexed top-down extraction worker for span `[i, j)` and nonterminal `nt`.

Recursion is structural on `fuel`; `fuel = j - i` suffices because well-formed backpointers give
both children strictly smaller widths.  Corrupt backpointers (out-of-range rule index or split)
can only exhaust fuel or miss a lookup and yield `none`, so the function is total either way.
A lexical entry becomes `.node lhs (.leaf tok) #[]`; a binary entry becomes
`.node lhs left #[right]`.
-/
def extractSpan {K : Type} (grammar : CNF K) (n : Nat) (back : Array Back) :
    Nat → Nat → Nat → NT → Option Tree
  | 0, _, _, _ => none
  | fuel + 1, i, j, nt =>
    match back.getD (Chart.cidx n grammar.nNT i j nt.toNat) .none with
    | .none => none
    | .lex ruleIdx =>
      (grammar.lex[ruleIdx.toNat]?).map fun rule ↦ Tree.node nt (.leaf rule.tok) #[]
    | .bin ruleIdx split =>
      match grammar.bin[ruleIdx.toNat]? with
      | none => none
      | some rule =>
        match extractSpan grammar n back fuel i split.toNat rule.r1,
            extractSpan grammar n back fuel split.toNat j rule.r2 with
        | some left, some right => some (Tree.node nt left #[right])
        | _, _ => none

/--
Total extraction of the recorded one-best tree over span `[i, j)` for nonterminal `nt`, from a
backpointer chart for a sentence of length `n`.  Returns `none` exactly when no complete
derivation was recorded for the entry (in particular whenever the cell's value is the semiring
zero).
-/
def extractTree {K : Type} (grammar : CNF K) (n : Nat) (back : Array Back)
    (i j : Nat) (nt : NT) : Option Tree :=
  extractSpan grammar n back (j - i) i j nt

/--
Run `ckyOneBest` and extract the goal derivation: the start symbol over the whole sentence.
`none` iff the sentence is rejected (goal value is the semiring zero) or empty.
-/
@[specialize]
def oneBestTree {K : Type} [SemiringOps K] [Inhabited K]
    (better : K → K → Bool) (grammar : CNF K) (words : Array Tok) : Option Tree :=
  let (_, back) := ckyOneBest better grammar words
  extractTree grammar words.size back 0 words.size grammar.start

/-- One folded subtree during `treeScore`: a bare terminal, or a completed scored constituent. -/
inductive Scored (K : Type) where
  /-- A bare leaf carrying its terminal; it is scored only by the parent's lexical rule. -/
  | terminal (tok : Tok)
  /-- A completed constituent of category `cat` with accumulated derivation weight `w`. -/
  | constituent (cat : Cat) (w : K)

/--
Fold one node for `treeScore`: match the node's shape against the grammar and semiring-sum every
production with the same left-hand side and right-hand side.  `Tree` deliberately erases
production identity, so duplicate same-shape productions denote alternative derivations of the
same displayed tree.  A node over a single bare leaf is scored by lexical rules; a node with
exactly two constituent children by binary rules; every other shape is not a CNF derivation.
-/
def scoreNode {K : Type} [SemiringOps K] (grammar : CNF K) (cat : Cat)
    (first : Option (Scored K)) (rest : Array (Option (Scored K))) : Option (Scored K) :=
  if rest.isEmpty then
    match first with
    | some (.terminal tok) =>
      let (matched, weight) := grammar.lex.foldl
        (fun (matched, weight) rule ↦
          if rule.lhs == cat && rule.tok == tok then (true, weight + rule.w)
          else (matched, weight))
        (false, 0)
      if matched then some (.constituent cat weight) else none
    | _ => none
  else if rest.size == 1 then
    match first, rest[0]! with
    | some (.constituent leftCat leftW), some (.constituent rightCat rightW) =>
      let (matched, weight) := grammar.bin.foldl
        (fun (matched, weight) rule ↦
          if rule.lhs == cat && rule.r1 == leftCat && rule.r2 == rightCat then
            (true, weight + rule.w)
          else (matched, weight))
        (false, 0)
      if matched then some (.constituent cat (weight * leftW * rightW)) else none
    | _, _ => none
  else none

/--
Spec-side score of a derivation tree: re-multiply (`⊗`) the weights of the grammar rules the
tree exhibits, bottom-up via `Tree.cata`.  `none` if any node fails to match a rule, or if the
root is a bare leaf.

This is the correctness gate for extraction: a `ckyOneBest`/`extractTree` run is correct when
`treeScore` of the extracted tree equals the chart's goal value.  All same-shape production
weights are combined with `⊕`, matching the alternatives that a production-identity-free tree
represents.
-/
def treeScore {K : Type} [SemiringOps K] (grammar : CNF K) (tree : Tree) : Option K :=
  match tree.cata (fun tok ↦ some (Scored.terminal tok)) (scoreNode grammar) with
  | some (.constituent _ w) => some w
  | _ => none

end Nlp.Parse
