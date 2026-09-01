import Nlp.Grammar.Induce

/-!
# Structural laws for treebank grammar induction

Weight conversion is deliberately separated from grammar structure. These laws make that
boundary explicit: changing the score carrier cannot change dense identifiers, generators, or
the reversible tree codec.
-/

namespace Nlp.TreebankGrammar

/-! ## Well-formed induced grammars -/

/-- No two positions in an array carry the same semantic key. -/
def KeyUnique (items : Array α) (key : α → κ) : Prop :=
  ∀ (left right : Nat) (leftBound : left < items.size)
      (rightBound : right < items.size),
    key items[left] = key items[right] → left = right

/--
The structural and weight contract shared by counted and probability grammars.

`symbols` is the size of the source interner. Dense parser nonterminals use a separate namespace,
while lexical tokens and source categories remain bounded by that interner.
-/
structure WF (symbols : Nat) (weightValid : K → Prop)
    (grammar : TreebankGrammar K) : Prop where
  symbolsCapacity : symbols ≤ UInt32.size
  nNT_eq : grammar.nNT = grammar.origins.size
  nNTCapacity : grammar.nNT ≤ UInt32.size
  startBound : grammar.start.toNat < grammar.nNT
  startReal : ∃ category, grammar.origin? grammar.start = some (.real category)
  realIndexExact : ∀ category nonterminal,
    grammar.realNT? category = some nonterminal ↔
      grammar.origin? nonterminal = some (.real category)
  syntheticIndexExact : ∀ key nonterminal,
    grammar.syntheticNT? key = some nonterminal ↔
      ∃ category, grammar.origin? nonterminal = some (.synthetic category key)
  originValid : ∀ index : Fin grammar.origins.size,
    match grammar.origins[index] with
    | .real category => category.toNat < symbols
    | .synthetic category key =>
        category.toNat < symbols ∧
        grammar.origin? key.parent = some (.real category) ∧
        key.parent.toNat < grammar.nNT ∧
        key.left.toNat < grammar.nNT ∧
        key.right.toNat < grammar.nNT
  binaryValid : ∀ index : Fin grammar.binary.size,
    let rule := grammar.binary[index]
    rule.lhs.toNat < grammar.nNT ∧
      rule.r1.toNat < grammar.nNT ∧
      rule.r2.toNat < grammar.nNT ∧ weightValid rule.w
  unaryValid : ∀ index : Fin grammar.unary.size,
    let rule := grammar.unary[index]
    rule.lhs.toNat < grammar.nNT ∧
      rule.rhs.toNat < grammar.nNT ∧ weightValid rule.w
  lexicalValid : ∀ index : Fin grammar.lexical.size,
    let rule := grammar.lexical[index]
    rule.lhs.toNat < grammar.nNT ∧
      rule.tok.toNat < symbols ∧ weightValid rule.w
  binaryUnique : KeyUnique grammar.binary fun rule ↦ (rule.lhs, rule.r1, rule.r2)
  unaryUnique : KeyUnique grammar.unary fun rule ↦ (rule.lhs, rule.rhs)
  lexicalUnique : KeyUnique grammar.lexical fun rule ↦ (rule.lhs, rule.tok)

/-- A counted grammar has strictly positive rule multiplicities. -/
abbrev CountWF (symbols : Nat) (grammar : TreebankGrammar Count) : Prop :=
  WF symbols (fun count ↦ 0 < count.toNat) grammar

/-- A checked probability is finite and belongs to the interval `(0, 1]`. -/
def ProbValid (probability : Prob) : Prop :=
  probability.toFloat.isFinite = true ∧
    0.0 < probability.toFloat ∧ probability.toFloat ≤ 1.0

/-- A probability grammar has finite, strictly positive, at-most-one rule weights. -/
abbrev ProbWF (symbols : Nat) (grammar : TreebankGrammar Prob) : Prop :=
  WF symbols ProbValid grammar

private theorem KeyUnique.map {items : Array α} {key : α → κ}
    (unique : KeyUnique items key) (convert : α → β)
    (targetKey : β → κ) (preserves : ∀ item, targetKey (convert item) = key item) :
    KeyUnique (items.map convert) targetKey := by
  intro left right leftBound rightBound equal
  simp only [Array.size_map] at leftBound rightBound
  apply unique left right leftBound rightBound
  simpa [preserves] using equal

/-! ## Weight-independent structure -/

variable {K L : Type} (f : K → L) (grammar : TreebankGrammar K)

@[simp] theorem mapWeights_start : (grammar.mapWeights f).start = grammar.start := rfl

@[simp] theorem mapWeights_nNT : (grammar.mapWeights f).nNT = grammar.nNT := rfl

@[simp] theorem mapWeights_origins : (grammar.mapWeights f).origins = grammar.origins := rfl

@[simp] theorem mapWeights_realIndex :
    (grammar.mapWeights f).realIndex = grammar.realIndex := rfl

@[simp] theorem mapWeights_syntheticIndex :
    (grammar.mapWeights f).syntheticIndex = grammar.syntheticIndex := rfl

@[simp] theorem mapWeights_binary_size :
    (grammar.mapWeights f).binary.size = grammar.binary.size := by
  simp [mapWeights]

@[simp] theorem mapWeights_unary_size :
    (grammar.mapWeights f).unary.size = grammar.unary.size := by
  simp [mapWeights]

@[simp] theorem mapWeights_lexical_size :
    (grammar.mapWeights f).lexical.size = grammar.lexical.size := by
  simp [mapWeights]

@[simp] theorem mapWeights_id : grammar.mapWeights id = grammar := by
  cases grammar
  simp [mapWeights]

/-- Consecutive weight conversions fuse without changing rule order or metadata. -/
theorem mapWeights_comp (next : L → M) :
    (grammar.mapWeights f).mapWeights next = grammar.mapWeights (next ∘ f) := by
  cases grammar
  simp [mapWeights, Array.map_map, Function.comp_def]

@[simp] theorem mapWeights_binary_getElem? (index : Nat) :
    (grammar.mapWeights f).binary[index]? =
      grammar.binary[index]?.map fun rule ↦ { rule with w := f rule.w } := by
  simp [mapWeights]

@[simp] theorem mapWeights_unary_getElem? (index : Nat) :
    (grammar.mapWeights f).unary[index]? =
      grammar.unary[index]?.map fun rule ↦ { rule with w := f rule.w } := by
  simp [mapWeights]

@[simp] theorem mapWeights_lexical_getElem? (index : Nat) :
    (grammar.mapWeights f).lexical[index]? =
      grammar.lexical[index]?.map fun rule ↦ { rule with w := f rule.w } := by
  simp [mapWeights]

@[simp] theorem origin?_mapWeights (nonterminal : NT) :
    (grammar.mapWeights f).origin? nonterminal = grammar.origin? nonterminal := rfl

@[simp] theorem realCat?_mapWeights (nonterminal : NT) :
    (grammar.mapWeights f).realCat? nonterminal = grammar.realCat? nonterminal := rfl

@[simp] theorem syntheticCat?_mapWeights (nonterminal : NT) :
    (grammar.mapWeights f).syntheticCat? nonterminal = grammar.syntheticCat? nonterminal := rfl

@[simp] theorem realNT?_mapWeights (category : Cat) :
    (grammar.mapWeights f).realNT? category = grammar.realNT? category := rfl

@[simp] theorem syntheticNT?_mapWeights (key : SyntheticKey) :
    (grammar.mapWeights f).syntheticNT? key = grammar.syntheticNT? key := rfl

/-- A weight conversion preserving the selected weight predicate preserves grammar WF. -/
theorem WF.mapWeights {symbols : Nat} {sourceValid : K → Prop}
    {targetValid : L → Prop} (wellFormed : WF symbols sourceValid grammar)
    (preserves : ∀ weight, sourceValid weight → targetValid (f weight)) :
    WF symbols targetValid (grammar.mapWeights f) := by
  refine {
    symbolsCapacity := wellFormed.symbolsCapacity
    nNT_eq := wellFormed.nNT_eq
    nNTCapacity := wellFormed.nNTCapacity
    startBound := wellFormed.startBound
    startReal := wellFormed.startReal
    realIndexExact := wellFormed.realIndexExact
    syntheticIndexExact := wellFormed.syntheticIndexExact
    originValid := wellFormed.originValid
    binaryValid := ?_
    unaryValid := ?_
    lexicalValid := ?_
    binaryUnique := ?_
    unaryUnique := ?_
    lexicalUnique := ?_
  }
  · change ∀ index : Fin (grammar.binary.map fun rule ↦
        { rule with w := f rule.w }).size,
      let rule := (grammar.binary.map fun rule ↦ { rule with w := f rule.w })[index]
      rule.lhs.toNat < grammar.nNT ∧ rule.r1.toNat < grammar.nNT ∧
        rule.r2.toNat < grammar.nNT ∧ targetValid rule.w
    intro index
    let sourceIndex : Fin grammar.binary.size := ⟨index, by simpa using index.isLt⟩
    rcases wellFormed.binaryValid sourceIndex with ⟨lhs, left, right, weight⟩
    simpa [sourceIndex] using
      And.intro lhs (And.intro left (And.intro right (preserves _ weight)))
  · change ∀ index : Fin (grammar.unary.map fun rule ↦
        { rule with w := f rule.w }).size,
      let rule := (grammar.unary.map fun rule ↦ { rule with w := f rule.w })[index]
      rule.lhs.toNat < grammar.nNT ∧ rule.rhs.toNat < grammar.nNT ∧
        targetValid rule.w
    intro index
    let sourceIndex : Fin grammar.unary.size := ⟨index, by simpa using index.isLt⟩
    rcases wellFormed.unaryValid sourceIndex with ⟨lhs, rhs, weight⟩
    simpa [sourceIndex] using And.intro lhs (And.intro rhs (preserves _ weight))
  · change ∀ index : Fin (grammar.lexical.map fun rule ↦
        { rule with w := f rule.w }).size,
      let rule := (grammar.lexical.map fun rule ↦ { rule with w := f rule.w })[index]
      rule.lhs.toNat < grammar.nNT ∧ rule.tok.toNat < symbols ∧ targetValid rule.w
    intro index
    let sourceIndex : Fin grammar.lexical.size := ⟨index, by simpa using index.isLt⟩
    rcases wellFormed.lexicalValid sourceIndex with ⟨lhs, token, weight⟩
    simpa [sourceIndex] using And.intro lhs (And.intro token (preserves _ weight))
  · change KeyUnique (grammar.binary.map fun rule ↦ { rule with w := f rule.w })
      fun rule ↦ (rule.lhs, rule.r1, rule.r2)
    exact KeyUnique.map wellFormed.binaryUnique
      (fun rule : BinRule K ↦ ({ rule with w := f rule.w } : BinRule L))
      (fun rule : BinRule L ↦ (rule.lhs, rule.r1, rule.r2)) (by intro; rfl)
  · change KeyUnique (grammar.unary.map fun rule ↦ { rule with w := f rule.w })
      fun rule ↦ (rule.lhs, rule.rhs)
    exact KeyUnique.map wellFormed.unaryUnique
      (fun rule : UnaryRule K ↦ ({ rule with w := f rule.w } : UnaryRule L))
      (fun rule : UnaryRule L ↦ (rule.lhs, rule.rhs)) (by intro; rfl)
  · change KeyUnique (grammar.lexical.map fun rule ↦ { rule with w := f rule.w })
      fun rule ↦ (rule.lhs, rule.tok)
    exact KeyUnique.map wellFormed.lexicalUnique
      (fun rule : LexRule K ↦ ({ rule with w := f rule.w } : LexRule L))
      (fun rule : LexRule L ↦ (rule.lhs, rule.tok)) (by intro; rfl)

@[simp] theorem toCFG_start : grammar.toCFG.start = grammar.start := rfl

@[simp] theorem toCFG_nNT : grammar.toCFG.nNT = grammar.nNT := rfl

@[simp] theorem toCFG_prods_size :
    grammar.toCFG.prods.size =
      grammar.binary.size + grammar.unary.size + grammar.lexical.size := by
  simp [toCFG, Nat.add_assoc]

/-- Forgetting induction metadata commutes with conversion of every rule weight. -/
theorem toCFG_mapWeights_prods :
    (grammar.mapWeights f).toCFG.prods =
      grammar.toCFG.prods.map fun rule ↦ { rule with w := f rule.w } := by
  simp [mapWeights, toCFG, Array.map_map, Array.map_append, Function.comp_def]

end Nlp.TreebankGrammar
