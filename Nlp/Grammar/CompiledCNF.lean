import Nlp.Grammar.IndexedCNF
import Std.Data.HashMap

/-!
# Validated compiled CNF grammars

`CompiledCNF` is the reusable parser-side representation of a `CNF`. Its constructor is hidden:
every public construction path is gated by a private-constructor certificate produced only after
validating every nonterminal identifier and capacity.

Lexical productions are stored in stable, contiguous token buckets. Binary productions use a
dense pair-offset table while it is small, then switch to a hash-indexed sparse table. The default
dense limit retains at most roughly 8 MiB of `Nat` offsets on a 64-bit runtime. Both layouts use
`Nat`/`UInt32` keys rather than boxed `Array UInt64` storage, and both preserve source order inside
each bucket.
-/

namespace Nlp

/-- Configuration for compiling a reusable CNF grammar. -/
structure CompileConfig where
  /-- Maximum number of `(left, right)` cells retained in a dense binary offset table. -/
  densePairCells : Nat := 1_048_576
deriving Repr, DecidableEq, Inhabited

/-- The production default keeps dense pair lookup through `1024 × 1024` nonterminals. -/
def CompileConfig.default : CompileConfig := {}

/-- The storage selected for the binary pair index. -/
inductive PairLayout where
  | dense
  | sparse
deriving Repr, DecidableEq, Inhabited

namespace CompileConfig

/-- Select dense storage exactly when the complete pair table fits the configured cell budget. -/
@[inline] def layoutFor (config : CompileConfig) (nNT : Nat) : PairLayout :=
  if nNT * nNT ≤ config.densePairCells then .dense else .sparse

@[simp] theorem layoutFor_eq_dense (config : CompileConfig) (nNT : Nat)
    (fits : nNT * nNT ≤ config.densePairCells) : config.layoutFor nNT = .dense := by
  simp [layoutFor, fits]

@[simp] theorem layoutFor_eq_sparse (config : CompileConfig) (nNT : Nat)
    (large : config.densePairCells < nNT * nNT) : config.layoutFor nNT = .sparse := by
  simp [layoutFor, Nat.not_le.mpr large]

end CompileConfig

/-- A typed failure produced before any grammar index is made observable. -/
inductive CompileError where
  | nonterminalCapacity (count : Nat)
  | binaryRuleCapacity (count : Nat)
  | lexicalRuleCapacity (count : Nat)
  | invalidStart (start : NT) (nNT : Nat)
  | invalidBinaryRule (source : Nat) (lhs left right : NT) (nNT : Nat)
  | invalidLexicalRule (source : Nat) (lhs : NT) (nNT : Nat)
deriving Repr, DecidableEq, Inhabited

/-- A checked half-open interval into one of the compiled rule arrays. -/
structure BucketRange where
  first : Nat
  stop : Nat
deriving Repr, DecidableEq, Inhabited

namespace BucketRange

/-- Number of entries in a valid compiled bucket. -/
@[inline] def size (range : BucketRange) : Nat := range.stop - range.first

end BucketRange

/-- One checked binary rule together with its position in the source `CNF.bin` array. -/
structure CompiledBinEntry (K : Type) where
  rule : BinRule K
  source : Nat
deriving Repr, Inhabited

/-- One checked lexical rule together with its position in the source `CNF.lex` array. -/
structure CompiledLexEntry (K : Type) where
  rule : LexRule K
  source : Nat
deriving Repr, Inhabited

/--
Internal binary bucket storage, exposed read-only for allocation-free parser loops.
-/
inductive BinaryIndex where
  /-- `starts[key]` and `starts[key + 1]` delimit a row-major pair bucket. -/
  | dense (starts : Array Nat)
  /-- Observed pair keys map to a bucket ordinal in the compact `starts` table. -/
  | sparse (ordinals : Std.HashMap Nat Nat) (keys starts : Array Nat)
deriving Inhabited

namespace BinaryIndex

/-- Which adaptive representation backs this index. -/
@[inline] def layout : BinaryIndex → PairLayout
  | .dense _ => .dense
  | .sparse _ _ _ => .sparse

end BinaryIndex

/--
A validated, reusable CNF grammar with stable lexical and binary indexes.

The private constructor is the invariant boundary. The arrays remain public because parser kernels
can safely cache them once and index them inside a checked `BucketRange` without accessor or
dictionary overhead.
-/
structure CompiledCNF (K : Type) where
  private mk ::
  grammar : CNF K
  binaryRules : Array (BinRule K)
  binarySources : Array Nat
  binaryIndex : BinaryIndex
  lexicalRules : Array (LexRule K)
  lexicalSources : Array Nat
  lexicalOrdinals : Std.HashMap Tok Nat
  lexicalKeys : Array Tok
  lexicalStarts : Array Nat

/--
A structurally validated CNF source awaiting index allocation.

The private constructor ensures that `grammar` has passed the complete identifier and capacity
scan. Callers may run additional validators over the exact retained grammar before choosing to
allocate compiled indexes.
-/
structure CheckedCNF (K : Type) where
  private mk ::
  /-- The exact source that passed structural validation. -/
  grammar : CNF K

namespace CompiledCNF

/-- Validate capacities shared by the compiler and effectful model-loading front ends. -/
def validateCapacities (nNT binaryRules lexicalRules : Nat) : Except CompileError Unit :=
  if UInt32.size < nNT then
    .error (.nonterminalCapacity nNT)
  else if UInt32.size < binaryRules then
    .error (.binaryRuleCapacity binaryRules)
  else if UInt32.size < lexicalRules then
    .error (.lexicalRuleCapacity lexicalRules)
  else
    .ok ()

/--
Validate all IDs once and retain the exact source without allocating either index.

Errors identify the first malformed source rule. The returned certificate can be inspected by
additional validators before `compileCheckedWith` allocates the adaptive indexes.
-/
def checkSource [Inhabited K] (grammar : CNF K) : Except CompileError (CheckedCNF K) := do
  validateCapacities grammar.nNT grammar.bin.size grammar.lex.size
  unless grammar.start.toNat < grammar.nNT do
    throw (.invalidStart grammar.start grammar.nNT)
  for source in [0:grammar.bin.size] do
    let rule := grammar.bin[source]!
    unless rule.lhs.toNat < grammar.nNT && rule.r1.toNat < grammar.nNT &&
        rule.r2.toNat < grammar.nNT do
      throw (.invalidBinaryRule source rule.lhs rule.r1 rule.r2 grammar.nNT)
  for source in [0:grammar.lex.size] do
    let rule := grammar.lex[source]!
    unless rule.lhs.toNat < grammar.nNT do
      throw (.invalidLexicalRule source rule.lhs grammar.nNT)
  return .mk grammar

/-- Validate all IDs before allocating either index. Errors identify the first source rule. -/
def validate [Inhabited K] (grammar : CNF K) : Except CompileError Unit := do
  let _ ← checkSource grammar
  return ()

private structure BinaryBuild (K : Type) where
  rules : Array (BinRule K)
  sources : Array Nat
  index : BinaryIndex

private structure LexicalBuild (K : Type) where
  rules : Array (LexRule K)
  sources : Array Nat
  ordinals : Std.HashMap Tok Nat
  keys : Array Tok
  starts : Array Nat

/-- Convert per-bucket counts to half-open starts. -/
private def prefixStarts (counts : Array Nat) : Array Nat := Id.run do
  let mut starts := Array.replicate (counts.size + 1) 0
  let mut total := 0
  for bucket in [0:counts.size] do
    starts := starts.set! bucket total
    total := total + counts[bucket]!
  starts := starts.set! counts.size total
  return starts

/-- Build a stable dense binary counting-sort index. -/
private def buildBinaryDense [Inhabited K] (grammar : CNF K) : BinaryBuild K := Id.run do
  let pairCount := grammar.nNT * grammar.nNT
  let mut counts := Array.replicate pairCount 0
  for rule in grammar.bin do
    let key := IndexedCNF.pairKey grammar.nNT rule.r1.toNat rule.r2.toNat
    counts := counts.modify key (fun count ↦ count + 1)
  let starts := prefixStarts counts
  let mut fill := starts
  let mut rules := Array.replicate grammar.bin.size default
  let mut sources := Array.replicate grammar.bin.size 0
  for source in [0:grammar.bin.size] do
    let rule := grammar.bin[source]!
    let key := IndexedCNF.pairKey grammar.nNT rule.r1.toNat rule.r2.toNat
    let target := fill[key]!
    rules := rules.set! target rule
    sources := sources.set! target source
    fill := fill.set! key (target + 1)
  return ⟨rules, sources, .dense starts⟩

/-- Build stable binary buckets for only the observed pairs. -/
private def buildBinarySparse [Inhabited K] (grammar : CNF K) : BinaryBuild K := Id.run do
  let mut ordinals : Std.HashMap Nat Nat :=
    Std.HashMap.emptyWithCapacity grammar.bin.size
  let mut keys : Array Nat := #[]
  let mut counts : Array Nat := #[]
  for rule in grammar.bin do
    let key := IndexedCNF.pairKey grammar.nNT rule.r1.toNat rule.r2.toNat
    match ordinals.get? key with
    | some bucket =>
      counts := counts.modify bucket (fun count ↦ count + 1)
    | none =>
      let bucket := counts.size
      ordinals := ordinals.insert key bucket
      keys := keys.push key
      counts := counts.push 1
  let starts := prefixStarts counts
  let mut fill := starts
  let mut rules := Array.replicate grammar.bin.size default
  let mut sources := Array.replicate grammar.bin.size 0
  for source in [0:grammar.bin.size] do
    let rule := grammar.bin[source]!
    let key := IndexedCNF.pairKey grammar.nNT rule.r1.toNat rule.r2.toNat
    let bucket := ordinals.getD key 0
    let target := fill[bucket]!
    rules := rules.set! target rule
    sources := sources.set! target source
    fill := fill.set! bucket (target + 1)
  return ⟨rules, sources, .sparse ordinals keys starts⟩

/-- Build stable contiguous lexical buckets keyed by token ID. -/
private def buildLexical [Inhabited K] (grammar : CNF K) : LexicalBuild K := Id.run do
  let mut ordinals : Std.HashMap Tok Nat :=
    Std.HashMap.emptyWithCapacity grammar.lex.size
  let mut keys : Array Tok := #[]
  let mut counts : Array Nat := #[]
  for rule in grammar.lex do
    match ordinals.get? rule.tok with
    | some bucket =>
      counts := counts.modify bucket (fun count ↦ count + 1)
    | none =>
      let bucket := counts.size
      ordinals := ordinals.insert rule.tok bucket
      keys := keys.push rule.tok
      counts := counts.push 1
  let starts := prefixStarts counts
  let mut fill := starts
  let mut rules := Array.replicate grammar.lex.size default
  let mut sources := Array.replicate grammar.lex.size 0
  for source in [0:grammar.lex.size] do
    let rule := grammar.lex[source]!
    let bucket := ordinals.getD rule.tok 0
    let target := fill[bucket]!
    rules := rules.set! target rule
    sources := sources.set! target source
    fill := fill.set! bucket (target + 1)
  return ⟨rules, sources, ordinals, keys, starts⟩

/-- Allocate adaptive indexes for an already structurally validated source without rescanning. -/
def compileCheckedWith [Inhabited K] (config : CompileConfig)
    (checked : CheckedCNF K) : CompiledCNF K :=
  let grammar := checked.grammar
  let binary :=
    match config.layoutFor grammar.nNT with
    | .dense => buildBinaryDense grammar
    | .sparse => buildBinarySparse grammar
  let lexical := buildLexical grammar
  .mk grammar binary.rules binary.sources binary.index lexical.rules lexical.sources
    lexical.ordinals lexical.keys lexical.starts

/-- Allocate production-threshold indexes for an already validated source without rescanning. -/
@[inline] def compileChecked [Inhabited K] (checked : CheckedCNF K) : CompiledCNF K :=
  compileCheckedWith CompileConfig.default checked

/-- Compile with an explicit dense-pair budget. Validation always precedes allocation. -/
def compileWith [Inhabited K] (config : CompileConfig) (grammar : CNF K) :
    Except CompileError (CompiledCNF K) := do
  let checked ← checkSource grammar
  return compileCheckedWith config checked

/-- Compile a CNF grammar using the production adaptive-index threshold. -/
@[inline] def compile [Inhabited K] (grammar : CNF K) :
    Except CompileError (CompiledCNF K) :=
  compileWith CompileConfig.default grammar

/-- Which adaptive binary index was selected. -/
@[inline] def pairLayout (compiled : CompiledCNF K) : PairLayout :=
  compiled.binaryIndex.layout

/-- Check and normalize a nonempty bucket range before exposing it to a parser loop. -/
private def checkedRange (starts : Array Nat) (bucket limit : Nat) : Option BucketRange :=
  match starts[bucket]?, starts[bucket + 1]? with
  | some first, some stop =>
    if first < stop ∧ stop ≤ limit then some ⟨first, stop⟩ else none
  | _, _ => none

/-- Checked lookup of a binary `(left, right)` bucket. Empty and invalid buckets return `none`. -/
@[inline] def binaryRange? (compiled : CompiledCNF K) (left right : NT) : Option BucketRange :=
  if left.toNat < compiled.grammar.nNT ∧ right.toNat < compiled.grammar.nNT then
    let key := IndexedCNF.pairKey compiled.grammar.nNT left.toNat right.toNat
    match compiled.binaryIndex with
    | .dense starts => checkedRange starts key compiled.binaryRules.size
    | .sparse ordinals _ starts =>
      (ordinals.get? key).bind fun bucket ↦
        checkedRange starts bucket compiled.binaryRules.size
  else
    none

/-- Checked lookup of a token's lexical bucket. Unknown tokens return `none`. -/
@[inline] def lexicalRange? (compiled : CompiledCNF K) (token : Tok) : Option BucketRange :=
  (compiled.lexicalOrdinals.get? token).bind fun bucket ↦
    checkedRange compiled.lexicalStarts bucket compiled.lexicalRules.size

/-- Checked parallel access to a compiled binary rule and its source position. -/
@[inline] def binaryEntry? (compiled : CompiledCNF K) (index : Nat) :
    Option (CompiledBinEntry K) :=
  compiled.binaryRules[index]?.bind fun rule ↦
    compiled.binarySources[index]?.map fun source ↦ ⟨rule, source⟩

/-- Checked parallel access to a compiled lexical rule and its source position. -/
@[inline] def lexicalEntry? (compiled : CompiledCNF K) (index : Nat) :
    Option (CompiledLexEntry K) :=
  compiled.lexicalRules[index]?.bind fun rule ↦
    compiled.lexicalSources[index]?.map fun source ↦ ⟨rule, source⟩

@[simp] theorem binaryRange?_left_oob (compiled : CompiledCNF K) (left right : NT)
    (outOfBounds : compiled.grammar.nNT ≤ left.toNat) :
    compiled.binaryRange? left right = none := by
  simp [binaryRange?, Nat.not_lt.mpr outOfBounds]

@[simp] theorem binaryRange?_right_oob (compiled : CompiledCNF K) (left right : NT)
    (outOfBounds : compiled.grammar.nNT ≤ right.toNat) :
    compiled.binaryRange? left right = none := by
  simp [binaryRange?, Nat.not_lt.mpr outOfBounds]

end CompiledCNF

/-- Compile a specification-side CNF into its validated reusable parser representation. -/
@[inline] def CNF.compile [Inhabited K] (grammar : CNF K) :
    Except CompileError (CompiledCNF K) :=
  CompiledCNF.compile grammar

end Nlp
