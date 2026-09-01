import Nlp.Core.Data.Interner
import Nlp.Core.Score.Count
import Nlp.Core.Score.Prob
import Nlp.Grammar.Binarize
import Nlp.Grammar.CNF

/-!
# Treebank grammar induction

Treebank induction counts lexical, unary, and binary productions in deterministic traversal order
and performs checked relative-frequency estimation per left-hand side.

The PTB reader interns words and category labels into one mixed namespace. Using those IDs directly
as CKY rows would make charts sparse and unnecessarily large, so only observed categories receive
dense parser nonterminals. A typed origin table distinguishes real categories from synthetic
right-spine categories and makes the pre-closure binary encoding reversible.

Unary productions remain explicit. Removing them without weighted closure and rule provenance
would change both the language and the restored parse trees.
-/

namespace Nlp

/-- A weighted unary production `lhs → rhs`. -/
structure UnaryRule (K : Type) where
  lhs : NT
  rhs : NT
  w : K
deriving Repr, Inhabited

/-- Exact structural generator for one synthetic right-spine nonterminal. -/
structure SyntheticKey where
  parent : NT
  left : NT
  right : NT
deriving Repr, DecidableEq, Hashable, Inhabited

/-- The source meaning of one dense parser nonterminal. -/
inductive NTOrigin where
  | real (category : Cat)
  | synthetic (category : Cat) (key : SyntheticKey)
deriving Repr, DecidableEq, Inhabited

/--
A densely coded binarized treebank grammar before unary closure.

The constructor is private because the origin array and both category indexes must agree. Rule
arrays are public and immutable, which keeps later closure and diagnostic passes allocation-light.
-/
structure TreebankGrammar (K : Type) where
  private mk ::
  binary : Array (BinRule K)
  unary : Array (UnaryRule K)
  lexical : Array (LexRule K)
  start : NT
  nNT : Nat
  origins : Array NTOrigin
  realIndex : Std.HashMap Cat NT
  syntheticIndex : Std.HashMap SyntheticKey NT
deriving Inhabited

/-- The production kind associated with a checked MLE failure. -/
inductive MleRuleKind where
  | binary
  | unary
  | lexical
deriving Repr, DecidableEq, Inhabited

/-- A numerical or count invariant rejected during relative-frequency estimation. -/
inductive MleError where
  | zeroCount (kind : MleRuleKind) (source : Nat)
  | zeroTotal (kind : MleRuleKind) (source : Nat) (lhs : NT)
  | countExceedsTotal (kind : MleRuleKind) (source count total : Nat)
  | invalidProbability (kind : MleRuleKind) (source count total : Nat) (bits : UInt64)
deriving Repr, DecidableEq, Inhabited

namespace TreebankGrammar

/-- Look up the typed origin of a dense nonterminal. -/
@[inline] def origin? (grammar : TreebankGrammar K) (nonterminal : NT) : Option NTOrigin :=
  grammar.origins[nonterminal.toNat]?

/-- Resolve a dense real nonterminal to its source treebank category. -/
@[inline] def realCat? (grammar : TreebankGrammar K) (nonterminal : NT) : Option Cat :=
  match grammar.origin? nonterminal with
  | some (.real category) => some category
  | _ => none

/-- Resolve a synthetic nonterminal to the real category whose right spine it represents. -/
@[inline] def syntheticCat? (grammar : TreebankGrammar K) (nonterminal : NT) : Option Cat :=
  match grammar.origin? nonterminal with
  | some (.synthetic category _) => some category
  | _ => none

/-- Resolve a source category to its dense real nonterminal. -/
@[inline] def realNT? (grammar : TreebankGrammar K) (category : Cat) : Option NT :=
  grammar.realIndex.get? category

/-- Resolve an exact synthetic structural generator to its dense nonterminal. -/
@[inline] def syntheticNT? (grammar : TreebankGrammar K) (key : SyntheticKey) : Option NT :=
  grammar.syntheticIndex.get? key

/-- Forget induction metadata and expose the unrestricted weighted-CFG specification view. -/
def toCFG (grammar : TreebankGrammar K) : CFG K :=
  let binary := grammar.binary.map fun rule ↦
    { lhs := rule.lhs, rhs := #[.nt rule.r1, .nt rule.r2], w := rule.w }
  let unary := grammar.unary.map fun rule ↦
    { lhs := rule.lhs, rhs := #[.nt rule.rhs], w := rule.w }
  let lexical := grammar.lexical.map fun rule ↦
    { lhs := rule.lhs, rhs := #[.tm rule.tok], w := rule.w }
  { prods := binary ++ unary ++ lexical, start := grammar.start, nNT := grammar.nNT }

/-- Apply a weight conversion without changing rule identity or category metadata. -/
def mapWeights (f : K → L) (grammar : TreebankGrammar K) : TreebankGrammar L :=
  .mk
    (grammar.binary.map fun rule ↦ { rule with w := f rule.w })
    (grammar.unary.map fun rule ↦ { rule with w := f rule.w })
    (grammar.lexical.map fun rule ↦ { rule with w := f rule.w })
    grammar.start grammar.nNT grammar.origins grammar.realIndex grammar.syntheticIndex

@[inline] private def addLhsCount (nNT : Nat) (totals : Array Nat)
    (lhs : NT) (count : Count) : Array Nat :=
  if lhs.toNat < nNT then
    totals.modify lhs.toNat (fun total ↦ total + count.toNat)
  else
    totals

private theorem addLhsCount_size (nNT : Nat) (totals : Array Nat)
    (lhs : NT) (count : Count) :
    (addLhsCount nNT totals lhs count).size = totals.size := by
  unfold addLhsCount
  split <;> simp

private theorem foldl_addLhsCount_size (nNT : Nat) (items : Array α)
    (lhs : α → NT) (count : α → Count) (totals : Array Nat) :
    (items.foldl (fun current item ↦
      addLhsCount nNT current (lhs item) (count item)) totals).size = totals.size := by
  apply Array.foldl_induction (as := items)
    (fun _ (current : Array Nat) ↦ current.size = totals.size) rfl
  intro index current size
  rw [addLhsCount_size, size]

/-- Exact outgoing count totals, one slot per dense nonterminal. -/
def lhsTotals (grammar : TreebankGrammar Count) : Array Nat :=
  let binary := grammar.binary.foldl
    (fun totals rule ↦ addLhsCount grammar.nNT totals rule.lhs rule.w)
    (Array.replicate grammar.nNT 0)
  let unary := grammar.unary.foldl
    (fun totals rule ↦ addLhsCount grammar.nNT totals rule.lhs rule.w)
    binary
  grammar.lexical.foldl
    (fun totals rule ↦ addLhsCount grammar.nNT totals rule.lhs rule.w)
    unary

/-- The outgoing-total table has exactly one slot per dense nonterminal. -/
@[simp] theorem lhsTotals_size (grammar : TreebankGrammar Count) :
    grammar.lhsTotals.size = grammar.nNT := by
  simp only [lhsTotals]
  rw [foldl_addLhsCount_size, foldl_addLhsCount_size, foldl_addLhsCount_size]
  exact Array.size_replicate

@[inline] private def relativeFrequency (kind : MleRuleKind) (source : Nat)
    (totals : Array Nat) (lhs : NT) (count : Count) : Except MleError Prob := do
  if count.toNat == 0 then
    throw (.zeroCount kind source)
  let total := totals.getD lhs.toNat 0
  if total == 0 then
    throw (.zeroTotal kind source lhs)
  if total < count.toNat then
    throw (.countExceedsTotal kind source count.toNat total)
  let value := Float.ofNat count.toNat / Float.ofNat total
  unless value.isFinite && decide (0.0 < value) && decide (value ≤ 1.0) do
    throw (.invalidProbability kind source count.toNat total value.toBits)
  return ⟨value⟩

/--
Checked relative-frequency estimation over all production kinds.

The pure induced grammar always satisfies these count invariants. The explicit error channel also
protects callers that used `mapWeights` to construct zero, inconsistent, or astronomically large
counts before requesting MLE.
-/
def mle (grammar : TreebankGrammar Count) : Except MleError (TreebankGrammar Prob) := do
  let totals := grammar.lhsTotals
  let binary ← grammar.binary.mapIdxM fun source rule ↦ do
    let weight ← relativeFrequency .binary source totals rule.lhs rule.w
    return { rule with w := weight }
  let unary ← grammar.unary.mapIdxM fun source rule ↦ do
    let weight ← relativeFrequency .unary source totals rule.lhs rule.w
    return { rule with w := weight }
  let lexical ← grammar.lexical.mapIdxM fun source rule ↦ do
    let weight ← relativeFrequency .lexical source totals rule.lhs rule.w
    return { rule with w := weight }
  return .mk binary unary lexical grammar.start grammar.nNT grammar.origins
    grammar.realIndex grammar.syntheticIndex

private structure RootedTree (T : Type) where
  tree : T
  root : Option NT

private def encodeBTreeAux? (grammar : TreebankGrammar K) :
    Grammar.BTree → Option (RootedTree Tree)
  | .leaf word => some ⟨.leaf word, none⟩
  | .unary category child => do
      let dense ← grammar.realNT? category
      let encoded ← grammar.encodeBTreeAux? child
      return ⟨.node dense encoded.tree #[], some dense⟩
  | .bin category left right => do
      let dense ← grammar.realNT? category
      let encodedLeft ← grammar.encodeBTreeAux? left
      let encodedRight ← grammar.encodeBTreeAux? right
      let _ ← encodedLeft.root
      let _ ← encodedRight.root
      return ⟨.node dense encodedLeft.tree #[encodedRight.tree], some dense⟩
  | .syn category left right => do
      let parent ← grammar.realNT? category
      let encodedLeft ← grammar.encodeBTreeAux? left
      let encodedRight ← grammar.encodeBTreeAux? right
      let leftRoot ← encodedLeft.root
      let rightRoot ← encodedRight.root
      let dense ← grammar.syntheticNT? ⟨parent, leftRoot, rightRoot⟩
      return ⟨.node dense encodedLeft.tree #[encodedRight.tree], some dense⟩

/-- Encode a typed binary tree using exact hash-consed synthetic generators. -/
def encodeBTree? (grammar : TreebankGrammar K) (tree : Grammar.BTree) : Option Tree :=
  (grammar.encodeBTreeAux? tree).map RootedTree.tree

/-- Decode a binary tree whose nodes still retain the pre-closure dense categories. -/
def decodeBTree? (grammar : TreebankGrammar K) (tree : Tree) : Option Grammar.BTree :=
  let decoded : Option (RootedTree Grammar.BTree) :=
    tree.cata (fun word ↦ some ⟨.leaf word, none⟩)
    fun nonterminal first rest ↦
    match grammar.origin? nonterminal with
    | some (.real category) =>
        if rest.isEmpty then
          first.map fun child ↦ ⟨.unary category child.tree, some nonterminal⟩
        else if rest.size == 1 then do
          let left ← first
          let right? ← rest[0]?
          let right ← right?
          let _ ← left.root
          let _ ← right.root
          return ⟨.bin category left.tree right.tree, some nonterminal⟩
        else
          none
    | some (.synthetic category key) =>
        if rest.size == 1 then do
          let left ← first
          let right? ← rest[0]?
          let right ← right?
          let leftRoot ← left.root
          let rightRoot ← right.root
          let parent ← grammar.realNT? category
          if key == ⟨parent, leftRoot, rightRoot⟩ then
            return ⟨.syn category left.tree right.tree, some nonterminal⟩
          else
            none
        else
          none
    | none => none
  decoded.map RootedTree.tree

/--
Decode and debinarize a directly encoded pre-closure tree.

This function intentionally makes no claim about trees produced after unary elimination. That
later transform must retain each source rule's unary path, and restoration must consume that
provenance rather than a production-identity-free `Tree`.
-/
def restoreEncodedTree? (grammar : TreebankGrammar K) (tree : Tree) : Option Tree :=
  (grammar.decodeBTree? tree).map Grammar.debinarize

end TreebankGrammar

namespace Grammar

/-- A typed treebank-induction failure. -/
inductive InduceError where
  | emptyTreebank
  | symbolCapacity (count : Nat)
  | nonterminalCapacity (count : Nat)
  | invalidStart (start : Cat) (symbols : Nat)
  | missingStart (start : Cat)
  | bareLeafRoot (tree : Nat) (word : Word)
  | syntheticRoot (tree : Nat) (category : Cat)
  | inconsistentRoot (tree : Nat) (expected actual : Cat)
  | categoryOutOfBounds (tree : Nat) (category : Cat) (symbols : Nat)
  | wordOutOfBounds (tree : Nat) (word : Word) (symbols : Nat)
  | terminalWhereConstituentExpected (tree : Nat) (word : Word)
deriving Repr, DecidableEq, Inhabited

private structure BinaryKey where
  lhs : NT
  left : NT
  right : NT
deriving DecidableEq, Hashable

private structure Builder where
  origins : Array NTOrigin := #[]
  realIndex : Std.HashMap Cat NT := {}
  syntheticIndex : Std.HashMap SyntheticKey NT := {}
  binary : Array (BinRule Count) := #[]
  unary : Array (UnaryRule Count) := #[]
  lexical : Array (LexRule Count) := #[]
  binaryIndex : Std.HashMap BinaryKey Nat := {}
  unaryIndex : Std.HashMap UInt64 Nat := {}
  lexicalIndex : Std.HashMap UInt64 Nat := {}

@[inline] private def pairKey (left right : UInt32) : UInt64 :=
  (left.toUInt64 <<< 32) ||| right.toUInt64

@[inline] private def increment (count : Count) : Count :=
  ⟨count.toNat + 1⟩

@[inline] private def validateCategory (tree symbols : Nat) (category : Cat) :
    Except InduceError Unit :=
  if category.toNat < symbols then
    .ok ()
  else
    .error (.categoryOutOfBounds tree category symbols)

@[inline] private def validateWord (tree symbols : Nat) (word : Word) :
    Except InduceError Unit :=
  if word.toNat < symbols then
    .ok ()
  else
    .error (.wordOutOfBounds tree word symbols)

private def Builder.ensureReal (builder : Builder) (symbols treeNumber : Nat)
    (category : Cat) : Except InduceError (Builder × NT) := do
  validateCategory treeNumber symbols category
  match builder.realIndex.get? category with
  | some nonterminal => return (builder, nonterminal)
  | none =>
      let identifier := builder.origins.size
      if _room : identifier < UInt32.size then
        let nonterminal := UInt32.ofNat identifier
        return ({ builder with
              origins := builder.origins.push (.real category)
              realIndex := builder.realIndex.insert category nonterminal },
          nonterminal)
      else
        throw (.nonterminalCapacity (identifier + 1))

private def Builder.ensureSynthetic (builder : Builder) (symbols treeNumber : Nat)
    (category : Cat) (key : SyntheticKey) : Except InduceError (Builder × NT) := do
  validateCategory treeNumber symbols category
  match builder.syntheticIndex.get? key with
  | some nonterminal => return (builder, nonterminal)
  | none =>
      let identifier := builder.origins.size
      if _room : identifier < UInt32.size then
        let nonterminal := UInt32.ofNat identifier
        return ({ builder with
              origins := builder.origins.push (.synthetic category key)
              syntheticIndex := builder.syntheticIndex.insert key nonterminal },
          nonterminal)
      else
        throw (.nonterminalCapacity (identifier + 1))

@[inline] private def Builder.addBinary (builder : Builder)
    (lhs left right : NT) : Builder :=
  let key := { lhs, left, right : BinaryKey }
  match builder.binaryIndex.get? key with
  | some index =>
      { builder with
        binary := builder.binary.modify index fun rule ↦
          { rule with w := increment rule.w } }
  | none =>
      let index := builder.binary.size
      { builder with
        binary := builder.binary.push ⟨lhs, left, right, ⟨1⟩⟩
        binaryIndex := builder.binaryIndex.insert key index }

@[inline] private def Builder.addUnary (builder : Builder) (lhs rhs : NT) : Builder :=
  let key := pairKey lhs rhs
  match builder.unaryIndex.get? key with
  | some index =>
      { builder with
        unary := builder.unary.modify index fun rule ↦
          { rule with w := increment rule.w } }
  | none =>
      let index := builder.unary.size
      { builder with
        unary := builder.unary.push ⟨lhs, rhs, ⟨1⟩⟩
        unaryIndex := builder.unaryIndex.insert key index }

@[inline] private def Builder.addLexical (builder : Builder)
    (lhs : NT) (word : Word) : Builder :=
  let key := pairKey lhs word
  match builder.lexicalIndex.get? key with
  | some index =>
      { builder with
        lexical := builder.lexical.modify index fun rule ↦
          { rule with w := increment rule.w } }
  | none =>
      let index := builder.lexical.size
      { builder with
        lexical := builder.lexical.push ⟨lhs, word, ⟨1⟩⟩
        lexicalIndex := builder.lexicalIndex.insert key index }

private def rootCategoryB (symbols treeNumber : Nat) : BTree → Except InduceError Cat
  | .leaf word => .error (.bareLeafRoot treeNumber word)
  | .unary category _ => do
      validateCategory treeNumber symbols category
      return category
  | .bin category _ _ => do
      validateCategory treeNumber symbols category
      return category
  | .syn category _ _ => .error (.syntheticRoot treeNumber category)

private inductive RootRef where
  | terminal (word : Word)
  | constituent (nonterminal : NT)

private def collectB (symbols treeNumber : Nat) :
    BTree → Builder → Except InduceError (Builder × RootRef)
  | .leaf word, builder => do
      validateWord treeNumber symbols word
      return (builder, .terminal word)
  | .unary category child, builder => do
      let (afterLhs, lhs) ← builder.ensureReal symbols treeNumber category
      let (afterChild, childRoot) ← collectB symbols treeNumber child afterLhs
      match childRoot with
      | .terminal word => return (afterChild.addLexical lhs word, .constituent lhs)
      | .constituent rhs => return (afterChild.addUnary lhs rhs, .constituent lhs)
  | .bin category left right, builder => do
      let (afterLhs, lhs) ← builder.ensureReal symbols treeNumber category
      let (afterLeft, leftRoot) ← collectB symbols treeNumber left afterLhs
      let (afterRight, rightRoot) ← collectB symbols treeNumber right afterLeft
      match leftRoot, rightRoot with
      | .constituent leftNT, .constituent rightNT =>
          return (afterRight.addBinary lhs leftNT rightNT, .constituent lhs)
      | .terminal word, _ | _, .terminal word =>
          throw (.terminalWhereConstituentExpected treeNumber word)
  | .syn category left right, builder => do
      let (afterParent, parent) ← builder.ensureReal symbols treeNumber category
      let (afterLeft, leftRoot) ← collectB symbols treeNumber left afterParent
      let (afterRight, rightRoot) ← collectB symbols treeNumber right afterLeft
      match leftRoot, rightRoot with
      | .constituent leftNT, .constituent rightNT =>
          let key : SyntheticKey := ⟨parent, leftNT, rightNT⟩
          let (afterSynthetic, lhs) ←
            afterRight.ensureSynthetic symbols treeNumber category key
          return (afterSynthetic.addBinary lhs leftNT rightNT, .constituent lhs)
      | .terminal word, _ | _, .terminal word =>
          throw (.terminalWhereConstituentExpected treeNumber word)

/-- Count a nonempty binarized treebank under an explicit, uniform source start category. -/
def induceBinarizedWithStart (interner : Interner) (start : Cat)
    (trees : Array BTree) : Except InduceError (TreebankGrammar Count) := do
  let symbols := interner.size
  if UInt32.size < symbols then
    throw (.symbolCapacity symbols)
  if trees.isEmpty then
    throw .emptyTreebank
  unless start.toNat < symbols do
    throw (.invalidStart start symbols)
  let (initial, startNT) ← ({} : Builder).ensureReal symbols 0 start
  let mut builder := initial
  for treeNumber in [0:trees.size] do
    let tree := trees[treeNumber]!
    let root ← rootCategoryB symbols treeNumber tree
    unless root == start do
      throw (.inconsistentRoot treeNumber start root)
    let (next, _) ← collectB symbols treeNumber tree builder
    builder := next
  return TreebankGrammar.mk builder.binary builder.unary builder.lexical startNT
    builder.origins.size builder.origins builder.realIndex builder.syntheticIndex

/-- Infer the source start category from the first binarized tree and require it throughout. -/
def induceBinarized (interner : Interner) (trees : Array BTree) :
    Except InduceError (TreebankGrammar Count) := do
  let first ←
    match trees[0]? with
    | some tree => pure tree
    | none => throw .emptyTreebank
  let start ← rootCategoryB interner.size 0 first
  induceBinarizedWithStart interner start trees

private def rootCategoryTree (symbols treeNumber : Nat) : Tree → Except InduceError Cat
  | .leaf word => .error (.bareLeafRoot treeNumber word)
  | .node category _ _ => do
      validateCategory treeNumber symbols category
      return category

/-- Count the virtual right-binarization of one ordinary tree without allocating a `BTree`. -/
private def collectTree (symbols treeNumber : Nat) :
    Tree → Builder → Except InduceError (Builder × RootRef)
  | .leaf word, builder => do
      validateWord treeNumber symbols word
      return (builder, .terminal word)
  | .node category child children, builder => do
      let (afterLhs, lhs) ← builder.ensureReal symbols treeNumber category
      let (afterFirst, firstRoot) ← collectTree symbols treeNumber child afterLhs
      let (afterChildren, childRoots) ← children.attach.foldl
        (fun result ⟨extra, _⟩ ↦ do
          let (current, roots) ← result
          let (next, root) ← collectTree symbols treeNumber extra current
          return (next, roots.push root))
        (.ok (afterFirst, #[]))
      if children.isEmpty then
        match firstRoot with
        | .terminal word =>
            return (afterChildren.addLexical lhs word, .constituent lhs)
        | .constituent rhs =>
            return (afterChildren.addUnary lhs rhs, .constituent lhs)
      else
        let firstNT ←
          match firstRoot with
          | .constituent nonterminal => pure nonterminal
          | .terminal word =>
              throw (.terminalWhereConstituentExpected treeNumber word)
        let mut roots := Array.emptyWithCapacity childRoots.size
        for root in childRoots do
          match root with
          | .constituent nonterminal => roots := roots.push nonterminal
          | .terminal word =>
              throw (.terminalWhereConstituentExpected treeNumber word)
        if roots.size == 1 then
          return (afterChildren.addBinary lhs firstNT roots[0]!, .constituent lhs)
        else
          let mut current := afterChildren
          let mut right := roots[roots.size - 1]!
          for offset in [0:roots.size - 1] do
            let index := roots.size - 2 - offset
            let left := roots[index]!
            let key : SyntheticKey := ⟨lhs, left, right⟩
            let (next, synthetic) ←
              current.ensureSynthetic symbols treeNumber category key
            current := next.addBinary synthetic left right
            right := synthetic
          return (current.addBinary lhs firstNT right, .constituent lhs)
termination_by tree => sizeOf tree
decreasing_by
  all_goals first | decreasing_trivial | (simp_wf; omega)

/--
Induce directly from ordinary trees without retaining a duplicate binarized treebank.

Only one tree's virtual right spine is examined at a time. Rule shapes and synthetic-node identity
are exactly those of `binarize`, but no intermediate `Array BTree` is allocated.
-/
def induceWithStart (interner : Interner) (start : Cat)
    (trees : Array Tree) : Except InduceError (TreebankGrammar Count) := do
  let symbols := interner.size
  if UInt32.size < symbols then
    throw (.symbolCapacity symbols)
  if trees.isEmpty then
    throw .emptyTreebank
  unless start.toNat < symbols do
    throw (.invalidStart start symbols)
  let (initial, startNT) ← ({} : Builder).ensureReal symbols 0 start
  let mut builder := initial
  for treeNumber in [0:trees.size] do
    let tree := trees[treeNumber]!
    let root ← rootCategoryTree symbols treeNumber tree
    unless root == start do
      throw (.inconsistentRoot treeNumber start root)
    let (next, _) ← collectTree symbols treeNumber tree builder
    builder := next
  return TreebankGrammar.mk builder.binary builder.unary builder.lexical startNT
    builder.origins.size builder.origins builder.realIndex builder.syntheticIndex

/-- Infer the start category from the first tree and induce its virtual right-binarization. -/
def induce (interner : Interner) (trees : Array Tree) :
    Except InduceError (TreebankGrammar Count) := do
  let first ←
    match trees[0]? with
    | some tree => pure tree
    | none => throw .emptyTreebank
  let start ← rootCategoryTree interner.size 0 first
  induceWithStart interner start trees

end Grammar
end Nlp
