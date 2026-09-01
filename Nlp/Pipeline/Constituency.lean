import Nlp.Pipeline.Annotate
import Nlp.Pipeline.Unary
import Nlp.Syntax.NamedTree

/-!
# Named constituency document annotation

The numeric CKY and restoration kernels remain the hot internal representation. A validated
`ConstituencyModel` binds them to an exact mixed treebank symbol table, an explicit lexical OOV
terminal, and self-contained named output trees. Documents are encoded once and parsed by
sentence range; the effectful facade adds policy, cancellation, and cubic-work scheduling.
-/

namespace Nlp

/-- A validated restored parser with exact lexical input and named tree output. -/
structure ConstituencyModel where
  private mk ::
  /-- Validated unary-aware numeric parsing kernel. -/
  parser : UnaryViterbiModel
  /-- Exact mixed treebank namespace used by category and terminal identifiers. -/
  symbols : Array String
  /-- Exact lexical forms occurring in at least one source lexical production. -/
  lexicalIds : Std.HashMap String Word
  /-- Checked lexical terminal used for forms absent from `lexicalIds`. -/
  oov : Word
  /-- Caller-supplied model identity retained for effectful diagnostics. -/
  diagnosticSource : String

namespace ConstituencyModel

/-- Why a treebank grammar and symbol table could not form a named parser. -/
inductive CompileError where
  | symbolCapacity (count : Nat)
  | emptySymbolName (index : Nat)
  | duplicateSymbolName (first duplicate : Nat) (name : String)
  | originCount (nonterminals origins : Nat)
  | categoryOutOfBounds (origin : Nat) (category : Cat) (symbols : Nat)
  | lexicalWordOutOfBounds (source : Nat) (word : Word) (symbols : Nat)
  | missingOovSymbol (name : String)
  | oovNotLexical (name : String) (symbol : Word)
  | unary (cause : UnaryViterbiCompileError)
deriving Repr

/-- A restored numeric tree unexpectedly escaped the validated symbol namespace. -/
inductive ParseError where
  | extraction (cause : ViterbiDerivationError)
  | restoration
  | categoryOutOfBounds (category : Cat) (symbols : Nat)
  | columnCount (forms words : Nat)
  | terminalOverflow (expected attempted : Nat)
  | terminalPosition (position forms words : Nat)
  | terminalMismatch (position : Nat) (expected found : Word)
  | terminalCount (expected found : Nat)
deriving Repr, DecidableEq, Inhabited

/-- Build a checked dense symbol index while retaining stable duplicate positions. -/
private def buildSymbolIndex (names : Array String) :
    Except CompileError (Std.HashMap String Word) := do
  if UInt32.size < names.size then
    throw <| .symbolCapacity names.size
  let mut ids : Std.HashMap String Word := Std.HashMap.emptyWithCapacity names.size
  for index in [0:names.size] do
    let name := names[index]!
    if name.isEmpty then
      throw <| .emptySymbolName index
    match ids.get? name with
    | some first => throw <| .duplicateSymbolName first.toNat index name
    | none => ids := ids.insert name (UInt32.ofNat index)
  return ids

/-- Validate category origins and build the exact lexical subset of the symbol table. -/
private def buildLexicalIndex (grammar : TreebankGrammar Vit) (names : Array String) :
    Except CompileError (Std.HashMap String Word) := do
  if grammar.origins.size != grammar.nNT then
    throw <| .originCount grammar.nNT grammar.origins.size
  for origin in [0:grammar.origins.size] do
    let category :=
      match grammar.origins[origin]! with
      | .real value | .synthetic value _ => value
    unless category.toNat < names.size do
      throw <| .categoryOutOfBounds origin category names.size
  let mut lexical : Std.HashMap String Word :=
    Std.HashMap.emptyWithCapacity grammar.lexical.size
  for source in [0:grammar.lexical.size] do
    let word := grammar.lexical[source]!.tok
    unless word.toNat < names.size do
      throw <| .lexicalWordOutOfBounds source word names.size
    lexical := lexical.insert names[word.toNat]! word
  return lexical

/--
Compile a named parser under explicit unary-expansion and adaptive-index policies.

The exact mixed namespace is retained by treebank induction. `oovName` must already occur in a
lexical production, so unknown forms never fabricate an unrecognizable numeric identifier.
-/
def compileWith (unaryConfig : UnaryElimConfig) (indexConfig : CompileConfig)
    (grammar : TreebankGrammar Vit) (oovName : String) :
    Except CompileError ConstituencyModel := do
  let symbols ← buildSymbolIndex grammar.symbols
  let lexicalIds ← buildLexicalIndex grammar grammar.symbols
  let oov ←
    match symbols.get? oovName with
    | some value => pure value
    | none => throw <| .missingOovSymbol oovName
  unless lexicalIds.get? oovName == some oov do
    throw <| .oovNotLexical oovName oov
  let parser ←
    match UnaryViterbiModel.compileWith unaryConfig indexConfig grammar with
    | .ok value => pure value
    | .error cause => throw <| .unary cause
  return .mk parser grammar.symbols lexicalIds oov "in-memory constituency grammar"

/-- Compile a named parser under production unary and adaptive-index policies. -/
@[inline] def compile (grammar : TreebankGrammar Vit) (oovName : String) :
    Except CompileError ConstituencyModel :=
  compileWith .default .default grammar oovName

/-- Replace only the diagnostic identity retained by the effectful boundary. -/
def withDiagnosticSource (model : ConstituencyModel) (source : String) : ConstituencyModel :=
  .mk model.parser model.symbols model.lexicalIds model.oov source

/-- Ordered mixed symbol names retained by the validated model. -/
@[inline] def symbolNames (model : ConstituencyModel) : Array String :=
  model.symbols

/-- Number of dense parser nonterminals used for chart policy. -/
@[inline] def nonterminalCount (model : ConstituencyModel) : Nat :=
  model.parser.nonterminalCount

/-- Encode one exact lexical form, falling back to the checked OOV terminal. -/
@[inline] def encode (model : ConstituencyModel) (form : String) : Word :=
  (model.lexicalIds.get? form).getD model.oov

/-- Encode a complete form column once for allocation-free sentence-range parsing. -/
def encodeForms (model : ConstituencyModel) (forms : Array String) : Array Word :=
  forms.map model.encode

/-- Form encoding preserves the complete source column length. -/
@[simp] theorem encodeForms_size (model : ConstituencyModel) (forms : Array String) :
    (model.encodeForms forms).size = forms.size := by
  simp [encodeForms]

/-- Resolve one restored subtree while threading its left-to-right terminal cursor. -/
private def resolveTreeRangeAux (model : ConstituencyModel) (forms : Array String)
    (words : Array Word) (lower length : Nat) :
    Tree → Nat → Except ParseError (NamedTree × Nat)
  | .leaf word, index => do
      if length ≤ index then
        throw <| ParseError.terminalOverflow length (index + 1)
      let position := lower + index
      let expected ←
        match words[position]? with
        | some value => pure value
        | none => throw <| ParseError.terminalPosition position forms.size words.size
      let form ←
        match forms[position]? with
        | some value => pure value
        | none => throw <| ParseError.terminalPosition position forms.size words.size
      unless expected == word do
        throw <| ParseError.terminalMismatch position expected word
      return (.leaf form, index + 1)
  | .node category child children, index => do
      let name ←
        match model.symbols[category.toNat]? with
        | some value => pure value
        | none => throw <| ParseError.categoryOutOfBounds category model.symbols.size
      let (namedChild, afterChild) ←
        resolveTreeRangeAux model forms words lower length child index
      let (namedChildren, next) ← children.attach.foldl
        (fun result ⟨extra, _⟩ ↦ do
          let (current, position) ← result
          let (named, after) ←
            resolveTreeRangeAux model forms words lower length extra position
          return (current.push named, after))
        (.ok (Array.emptyWithCapacity children.size, afterChild))
      return (.node name namedChild namedChildren, next)
termination_by tree _ => sizeOf tree
decreasing_by
  all_goals first | decreasing_trivial | (simp_wf; omega)

/-- Shifting the initial value shifts an additive left fold by the same amount. -/
private theorem foldlMeasure_add (measure : α → Nat) : ∀ trees : List α, ∀ initial : Nat,
    trees.foldl (fun total item ↦ total + measure item) initial =
      initial + trees.foldl (fun total item ↦ total + measure item) 0
  | [], initial => by simp
  | item :: items, initial => by
      simp only [List.foldl_cons]
      rw [foldlMeasure_add measure items (initial + measure item)]
      have shifted := foldlMeasure_add measure items (measure item)
      simp only [Nat.zero_add]
      rw [shifted]
      omega

/-- A left fold whose step preserves errors remains at its initial error. -/
private theorem foldlExceptError (step : Except ε α → β → Except ε α)
    (preserves : ∀ error item, step (.error error) item = .error error) :
    ∀ items : List β, ∀ error, items.foldl step (.error error) = .error error
  | [], _ => rfl
  | item :: items, error => by
      simp only [List.foldl_cons, preserves error item]
      exact foldlExceptError step preserves items error

/-- Successful child resolution advances by width and appends exactly the covered form range. -/
private theorem resolveTreeRangeAux_children
    (model : ConstituencyModel) (forms : Array String) (words : Array Word)
    (lower length : Nat) (children : Array Tree) : ∀ trees : List {tree // tree ∈ children},
      (∀ extra : {tree // tree ∈ children}, ∀ index named next,
        resolveTreeRangeAux model forms words lower length extra.1 index = .ok (named, next) →
          next = index + extra.1.width ∧
            named.yieldForms = forms.extract (lower + index) (lower + next)) →
      ∀ (current : Array NamedTree) (position : Nat) (output : Array NamedTree) (next : Nat),
        trees.foldl (fun (result : Except ParseError (Array NamedTree × Nat)) extra ↦ do
          let (namedTrees, cursor) ← result
          let (named, after) ←
            resolveTreeRangeAux model forms words lower length extra.1 cursor
          return (namedTrees.push named, after)) (.ok (current, position)) =
            .ok (output, next) →
          next = position + trees.foldl (fun total extra ↦ total + extra.1.width) 0 ∧
            ∀ initial : Array String,
              output.foldl (fun result tree ↦ result ++ tree.yieldForms) initial =
                current.foldl (fun result tree ↦ result ++ tree.yieldForms) initial ++
                  forms.extract (lower + position) (lower + next)
  | [], _, current, position, output, next, success => by
      simp only [List.foldl_nil] at success
      cases success
      refine ⟨by simp, ?_⟩
      intro initial
      rw [Array.extract_empty_of_stop_le_start (Nat.le_refl _), Array.append_empty]
  | tree :: trees, hypothesis, current, position, output, next, success => by
      simp only [List.foldl_cons] at success
      let step : Except ParseError (Array NamedTree × Nat) →
          {tree // tree ∈ children} → Except ParseError (Array NamedTree × Nat) :=
        fun result extra ↦ do
          let (namedTrees, cursor) ← result
          let (named, after) ←
            resolveTreeRangeAux model forms words lower length extra.1 cursor
          return (namedTrees.push named, after)
      change trees.foldl step (step (.ok (current, position)) tree) =
        .ok (output, next) at success
      cases resolved : resolveTreeRangeAux model forms words lower length tree.1 position with
      | error cause =>
          have firstFailed : step (.ok (current, position)) tree = .error cause := by
            simp [step, resolved, bind, Except.bind]
          rw [firstFailed] at success
          have failed := foldlExceptError step (by
            intro error extra
            simp [step, bind, Except.bind]) trees cause
          rw [failed] at success
          contradiction
      | ok result =>
          rcases result with ⟨named, after⟩
          have firstSuccess : step (.ok (current, position)) tree =
                .ok (current.push named, after) := by
            simp [step, resolved, pure, Except.pure, bind, Except.bind]
          rw [firstSuccess] at success
          have tailSuccess := success
          change trees.foldl
            (fun (result : Except ParseError (Array NamedTree × Nat)) extra ↦ do
            let (namedTrees, cursor) ← result
            let (named, after) ←
              resolveTreeRangeAux model forms words lower length extra.1 cursor
            return (namedTrees.push named, after))
              (.ok (current.push named, after)) = .ok (output, next) at tailSuccess
          have first := hypothesis tree position named after resolved
          have rest := resolveTreeRangeAux_children model forms words lower length children trees
            hypothesis
            (current.push named) after output next tailSuccess
          refine ⟨?_, ?_⟩
          · rw [rest.1, first.1]
            simp only [List.foldl_cons]
            rw [Nat.zero_add]
            change position + tree.1.width +
                trees.foldl (fun total extra ↦ total + extra.1.width) 0 =
              position + trees.foldl (fun total extra ↦ total + extra.1.width)
                tree.1.width
            rw [foldlMeasure_add (fun extra : {tree // tree ∈ children} ↦ extra.1.width)
              trees tree.1.width]
            omega
          · intro initial
            rw [rest.2 initial, Array.foldl_push, first.2, Array.append_assoc]
            rw [Array.extract_append_extract]
            congr <;> omega

/-- Successful recursive resolution preserves its exact form range and advances by tree width. -/
private theorem resolveTreeRangeAux_spec (model : ConstituencyModel)
    (forms : Array String) (words : Array Word) (lower length : Nat) :
    ∀ tree index named next,
      resolveTreeRangeAux model forms words lower length tree index = .ok (named, next) →
        next = index + tree.width ∧
          named.yieldForms = forms.extract (lower + index) (lower + next) := by
  intro tree
  induction tree using Tree.inductionOn with
  | leaf word =>
      intro index named next success
      by_cases overflow : length ≤ index
      · simp [resolveTreeRangeAux, overflow, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at success
      · cases wordAt : words[lower + index]? with
        | none =>
            simp [resolveTreeRangeAux, overflow, wordAt, bind,
              Except.bind, throw, throwThe, MonadExceptOf.throw] at success
        | some expected =>
            cases formAt : forms[lower + index]? with
            | none =>
                simp [resolveTreeRangeAux, overflow, wordAt, formAt, pure, Except.pure,
                  bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at success
            | some form =>
                by_cases sameWord : expected = word
                · subst expected
                  simp [resolveTreeRangeAux, overflow, wordAt, formAt, pure, Except.pure,
                    bind, Except.bind] at success
                  rcases success with ⟨rfl, rfl⟩
                  constructor
                  · simp [Tree.width]
                  · simp only [NamedTree.yieldForms_leaf]
                    have bound : lower + index < forms.size :=
                      (Array.getElem?_eq_some_iff.mp formAt).choose
                    rw [show lower + (index + 1) = lower + index + 1 by omega]
                    rw [Array.extract_succ_right (by omega) bound]
                    have value := (Array.getElem?_eq_some_iff.mp formAt).choose_spec
                    rw [value]
                    rw [Array.extract_empty_of_stop_le_start (Nat.le_refl _)]
                    rfl
                · simp [resolveTreeRangeAux, overflow, wordAt, formAt, sameWord, pure,
                    Except.pure, bind, Except.bind, throw, throwThe,
                    MonadExceptOf.throw] at success
  | node category child children childIH childrenIH =>
      intro index named next success
      cases categoryAt : model.symbols[category.toNat]? with
      | none =>
          have impossible : False := by
            simp [resolveTreeRangeAux, categoryAt, bind, Except.bind, throw, throwThe,
              MonadExceptOf.throw] at success
          contradiction
      | some name =>
        cases childResolved :
            resolveTreeRangeAux model forms words lower length child index with
        | error cause =>
            have impossible : False := by
              simp [resolveTreeRangeAux, categoryAt, childResolved, pure, Except.pure,
                bind, Except.bind] at success
            contradiction
        | ok result =>
            rcases result with ⟨namedChild, afterChild⟩
            let step : Except ParseError (Array NamedTree × Nat) → Tree →
                Except ParseError (Array NamedTree × Nat) :=
              fun result extra ↦ do
                let (current, position) ← result
                let (named, after) ←
                  resolveTreeRangeAux model forms words lower length extra position
                return (current.push named, after)
            have normalizedSuccess :
                (do
                  let (namedChildren, afterChildren) ←
                    children.foldl step (.ok (#[], afterChild))
                  return (NamedTree.node name namedChild namedChildren, afterChildren)) =
                    .ok (named, next) := by
              simpa [resolveTreeRangeAux, categoryAt, childResolved, step,
                Array.emptyWithCapacity_eq, pure, Except.pure, bind, Except.bind] using success
            cases childrenResolved : children.foldl step (.ok (#[], afterChild)) with
            | error cause =>
                rw [childrenResolved] at normalizedSuccess
                contradiction
            | ok result =>
                rcases result with ⟨namedChildren, afterChildren⟩
                rw [childrenResolved] at normalizedSuccess
                change Except.ok
                    (NamedTree.node name namedChild namedChildren, afterChildren) =
                  Except.ok (named, next) at normalizedSuccess
                have pairEq := Except.ok.inj normalizedSuccess
                have namedEq : NamedTree.node name namedChild namedChildren = named :=
                  congrArg Prod.fst pairEq
                have nextEq : afterChildren = next := congrArg Prod.snd pairEq
                subst named
                subst next
                have first := childIH index namedChild afterChild childResolved
                have attachedResolved :
                    children.attach.foldl
                        (fun (result : Except ParseError (Array NamedTree × Nat)) extra ↦ do
                          let (current, position) ← result
                          let (named, after) ← resolveTreeRangeAux model forms words
                            lower length extra.1 position
                          return (current.push named, after))
                        (.ok (Array.emptyWithCapacity children.size, afterChild)) =
                      .ok (namedChildren, afterChildren) := by
                  rw [Array.foldl_attach
                    (f := fun (result : Except ParseError (Array NamedTree × Nat)) extra ↦ do
                    let (current, position) ← result
                    let (named, after) ← resolveTreeRangeAux model forms words
                      lower length extra position
                    return (current.push named, after))]
                  simpa [step, Array.emptyWithCapacity_eq] using childrenResolved
                have rest := resolveTreeRangeAux_children model forms words lower length
                  children children.attach.toList
                  (fun extra ↦ childrenIH extra.1 extra.2)
                  #[] afterChild namedChildren afterChildren (by
                    simpa [Array.emptyWithCapacity_eq, Array.foldl_toList]
                      using attachedResolved)
                constructor
                · rw [rest.1, first.1, Tree.width_node]
                  rw [← Array.foldl_attach
                    (f := fun total (tree : Tree) ↦ total + tree.width)]
                  rw [← Array.foldl_toList]
                  rw [foldlMeasure_add
                    (fun extra : {tree // tree ∈ children} ↦ extra.1.width)
                    children.attach.toList child.width]
                  omega
                · rw [NamedTree.yieldForms_node]
                  rw [rest.2 namedChild.yieldForms]
                  simp only [Array.foldl_empty, first.2]
                  rw [Array.extract_append_extract]
                  congr <;> omega

/-- Resolve a restored tree against one original-form and encoded-token range. -/
def resolveTreeRange (model : ConstituencyModel) (forms : Array String)
    (words : Array Word) (start stop : Nat) (tree : Tree) :
    Except ParseError NamedTree :=
  if _columns : forms.size = words.size then
    let upper := min stop words.size
    let lower := min start upper
    let length := upper - lower
    if _width : tree.width = length then
      match resolveTreeRangeAux model forms words lower length tree 0 with
      | .error cause => .error cause
      | .ok (named, found) =>
          if found = length then .ok named else .error (.terminalCount length found)
    else
      .error (.terminalCount length tree.width)
  else
    .error (.columnCount forms.size words.size)

/-- Successful tree resolution certifies aligned columns and exact normalized input width. -/
theorem resolveTreeRange_input_invariants (model : ConstituencyModel)
    (forms : Array String) (words : Array Word) (start stop : Nat) (tree : Tree)
    {named : NamedTree} (resolved :
      model.resolveTreeRange forms words start stop tree = .ok named) :
    forms.size = words.size ∧
      tree.width = Parse.Viterbi.rangeLength words start stop := by
  by_cases columns : forms.size = words.size
  · refine ⟨columns, ?_⟩
    by_cases width : tree.width = Parse.Viterbi.rangeLength words start stop
    · exact width
    · change tree.width ≠ min stop words.size - min start (min stop words.size) at width
      simp [resolveTreeRange, columns, width] at resolved
  · simp [resolveTreeRange, columns] at resolved

/-- Successful tree resolution preserves the exact normalized source-form range as its yield. -/
theorem resolveTreeRange_yieldForms (model : ConstituencyModel)
    (forms : Array String) (words : Array Word) (start stop : Nat) (tree : Tree)
    {named : NamedTree} (resolved :
      model.resolveTreeRange forms words start stop tree = .ok named) :
    named.yieldForms =
      forms.extract (min start (min stop forms.size)) (min stop forms.size) := by
  have invariants := model.resolveTreeRange_input_invariants forms words start stop tree resolved
  let upper := min stop words.size
  let lower := min start upper
  let length := upper - lower
  have width : tree.width = length := by
    simpa [Parse.Viterbi.rangeLength, upper, lower, length] using invariants.2
  rw [invariants.1]
  cases auxiliary : resolveTreeRangeAux model forms words lower length tree 0 with
  | error cause =>
      simp [resolveTreeRange, invariants.1, upper, lower, length, width, auxiliary]
        at resolved
  | ok result =>
      rcases result with ⟨candidate, found⟩
      by_cases count : found = length
      · have candidateEq : candidate = named := by
          simpa [resolveTreeRange, invariants.1, upper, lower, length, width,
            auxiliary, count] using resolved
        subst named
        have exactRange := resolveTreeRangeAux_spec model forms words lower length
          tree 0 candidate found auxiliary
        rw [exactRange.2, count]
        change forms.extract lower (lower + length) = forms.extract lower upper
        have lowerLeUpper : lower ≤ upper := Nat.min_le_right start upper
        rw [Nat.add_sub_of_le lowerLeUpper]
      · simp [resolveTreeRange, invariants.1, upper, lower, length, width,
          auxiliary, count] at resolved

/-- Resolve a restored tree against complete aligned form and encoded-token columns. -/
@[inline] def resolveTree (model : ConstituencyModel) (forms : Array String)
    (words : Array Word) (tree : Tree) : Except ParseError NamedTree :=
  model.resolveTreeRange forms words 0 words.size tree

/-- Successful full-column tree resolution preserves the complete source-form yield. -/
theorem resolveTree_yieldForms (model : ConstituencyModel)
    (forms : Array String) (words : Array Word) (tree : Tree) {named : NamedTree}
    (resolved : model.resolveTree forms words tree = .ok named) :
    named.yieldForms = forms := by
  have ranged : model.resolveTreeRange forms words 0 words.size tree = .ok named := by
    simpa [resolveTree] using resolved
  have columns := model.resolveTreeRange_input_invariants forms words 0 words.size tree ranged
  have exactYield := model.resolveTreeRange_yieldForms forms words 0 words.size tree ranged
  rw [← columns.1] at exactYield
  simpa using exactYield

/-- Parse one normalized encode-once range and resolve its exact restored tree. -/
def parseEncodedRange? (model : ConstituencyModel) (forms : Array String)
    (words : Array Word) (start stop : Nat) : Except ParseError (Option NamedTree) :=
  if forms.size != words.size then
    .error (.columnCount forms.size words.size)
  else
    match model.parser.derivationRangeChecked? words start stop with
    | .error cause => .error (.extraction cause)
    | .ok none => .ok none
    | .ok (some derivation) =>
        match model.parser.restoreDerivation? derivation with
        | none => .error .restoration
        | some tree => model.resolveTreeRange forms words start stop tree |>.map some

/-- Encode once, parse one normalized form range, and resolve its named tree. -/
def parseFormsRange? (model : ConstituencyModel) (forms : Array String)
    (start stop : Nat) : Except ParseError (Option NamedTree) :=
  model.parseEncodedRange? forms (model.encodeForms forms) start stop

/-- Parse a complete form sequence through the pure functional API. -/
@[inline] def parseForms? (model : ConstituencyModel) (forms : Array String) :
    Except ParseError (Option NamedTree) :=
  model.parseFormsRange? forms 0 forms.size

/-- A checked document could not be converted into named constituency output. -/
inductive DocumentError where
  | input (cause : Doc.SemanticError)
  | tree (sentence start stop : Nat) (cause : ParseError)
  | sentenceCount (expected found : Nat)
  | output (cause : Doc.SemanticError)
deriving Repr

/-- Validate and attach exactly one named tree to every advertised sentence. -/
def assembleDocument (doc : Doc available) (trees : Array NamedTree)
    (_requirements : Sub [.tokens, .sents] available := by decide) :
    Except DocumentError (Doc (.parse :: available)) := do
  let expected := doc.sentenceRanges.size
  if trees.size != expected then
    throw <| .sentenceCount expected trees.size
  let output : Doc (.parse :: available) := { doc with parse := trees }
  match output.checkedSemantic with
  | .ok checked => pure checked
  | .error cause => throw <| .output cause

/--
Parse every advertised sentence through the pure functional API.

The form column is encoded once. The first sentence without a complete derivation makes the
document result `none`; model or document invariant failures remain distinct typed errors.
-/
def parseDocument? (model : ConstituencyModel) (doc : Doc available)
    (_requirements : Sub [.tokens, .sents] available := by decide) :
    Except DocumentError (Option (Doc (.parse :: available))) := do
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause => throw <| .input cause
  let ranges := checked.sentenceRanges
  let words := model.encodeForms checked.forms
  let mut trees := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    let (start, stop) := ranges[sentence]!
    let tree ←
      match model.parseEncodedRange? checked.forms words start stop with
      | .ok value => pure value
      | .error cause => throw <| .tree sentence start stop cause
    match tree with
    | none => return none
    | some value => trees := trees.push value
  return some (← assembleDocument checked trees _requirements)

end ConstituencyModel

namespace NLP

/-- Stable rendering for named constituency model compilation failures. -/
def constituencyCompileErrorDetail : ConstituencyModel.CompileError → String
  | .symbolCapacity count =>
      s!"constituency symbol count {count} exceeds the UInt32 identifier capacity"
  | .emptySymbolName index => s!"constituency symbol {index} is empty"
  | .duplicateSymbolName first duplicate name =>
      s!"constituency symbol {duplicate} duplicates symbol {first}: {repr name}"
  | .originCount nonterminals origins =>
      s!"constituency grammar declares {nonterminals} nonterminals but has {origins} origins"
  | .categoryOutOfBounds origin category symbols =>
      s!"constituency origin {origin} uses category {category.toNat} outside [0, {symbols})"
  | .lexicalWordOutOfBounds source word symbols =>
      s!"constituency lexical rule {source} uses word {word.toNat} outside [0, {symbols})"
  | .missingOovSymbol name =>
      s!"constituency OOV symbol {repr name} is absent from the mixed symbol table"
  | .oovNotLexical name symbol =>
      s!"constituency OOV symbol {repr name} at {symbol.toNat} has no lexical production"
  | .unary cause => unaryViterbiCompileErrorDetail cause

/-- Stable rendering for impossible post-compilation tree-resolution failures. -/
def constituencyParseErrorDetail : ConstituencyModel.ParseError → String
  | .extraction cause => viterbiDerivationErrorDetail cause
  | .restoration => "exact emitted derivation failed source-provenance restoration"
  | .categoryOutOfBounds category symbols =>
      s!"restored category {category.toNat} is outside [0, {symbols})"
  | .columnCount forms words =>
      s!"constituency form/word columns disagree: forms={forms}, words={words}"
  | .terminalOverflow expected attempted =>
      s!"restored tree cursor attempted terminal {attempted}; expected {expected}"
  | .terminalPosition position forms words =>
      s!"restored terminal position {position} is outside forms={forms}, words={words}"
  | .terminalMismatch position expected found =>
      s!"restored terminal {position} changed encoded word " ++
        s!"{expected.toNat} to {found.toNat}"
  | .terminalCount expected found =>
      s!"restored tree has {found} terminals; expected {expected}"

/-- Compile a named constituency model with explicit unary and adaptive-index policies. -/
def compileConstituencyModelWith (unaryConfig : UnaryElimConfig)
    (indexConfig : CompileConfig) (grammar : TreebankGrammar Vit)
    (oovName : String)
    (source : String := "in-memory constituency grammar") : NLP ConstituencyModel := do
  checkCancelled
  let model ←
    match ConstituencyModel.compileWith unaryConfig indexConfig grammar oovName with
    | .ok value => pure (value.withDiagnosticSource source)
    | .error cause => throw <| .modelCorrupt source (constituencyCompileErrorDetail cause)
  checkCancelled
  return model

/-- Compile a named constituency model under production parser policies. -/
@[inline] def compileConstituencyModel (grammar : TreebankGrammar Vit) (oovName : String)
    (source : String := "in-memory constituency grammar") : NLP ConstituencyModel :=
  compileConstituencyModelWith .default .default grammar oovName source

/-- Parse one checked document with cancellation between sentence kernels. -/
def parseConstituency (model : ConstituencyModel) (doc : Doc available)
    (_requirements : Sub [.tokens, .sents] available := by decide) :
    NLP (Analysis (Doc (.parse :: available))) := do
  checkCancelled
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause =>
      throw <| .invalidInput "constituency parser input"
        s!"semantic validation failed: {repr cause}"
  let ranges := checked.sentenceRanges
  let config := (← read).config
  for range in ranges do
    if let some reason :=
        chartSkipReason? config model.nonterminalCount (range.2 - range.1) then
      return .skipped reason
  let words := model.encodeForms checked.forms
  let mut trees := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    checkCancelled
    let (start, stop) := ranges[sentence]!
    let parsed := model.parseEncodedRange? checked.forms words start stop
    checkCancelled
    match parsed with
    | .ok none => return .noAnalysis
    | .ok (some tree) => trees := trees.push tree
    | .error cause =>
      throw <| .modelCorrupt model.diagnosticSource <|
        s!"sentence {sentence} tokens [{start}, {stop}): " ++
          constituencyParseErrorDetail cause
  checkCancelled
  match ConstituencyModel.assembleDocument checked trees _requirements with
  | .ok output => return .ok output
  | .error cause =>
    throw <| .modelCorrupt model.diagnosticSource <|
      s!"constituency extraction violated its checked document invariant: {repr cause}"

/-- Parse documents with an explicit minimum cubic-work scheduling unit. -/
@[inline] def parseConstituencyManyWithMinWork (minWork : Nat)
    (model : ConstituencyModel) (documents : Array (Doc available))
    (requirements : Sub [.tokens, .sents] available := by decide) :
    NLP (Array (Analysis (Doc (.parse :: available)))) :=
  traverseArrayWeightedWithMinWeight minWork documents Doc.sentenceCubicWork fun doc ↦
    parseConstituency model doc requirements

/-- Parse documents with bounded cubic-work concurrency and stable input order. -/
@[inline] def parseConstituencyMany (model : ConstituencyModel)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens, .sents] available := by decide) :
    NLP (Array (Analysis (Doc (.parse :: available)))) :=
  traverseArrayWeighted documents Doc.sentenceCubicWork fun doc ↦
    parseConstituency model doc requirements

end NLP
end Nlp
