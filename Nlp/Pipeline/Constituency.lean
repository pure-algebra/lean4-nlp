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

/-- Resolve a restored tree against complete aligned form and encoded-token columns. -/
@[inline] def resolveTree (model : ConstituencyModel) (forms : Array String)
    (words : Array Word) (tree : Tree) : Except ParseError NamedTree :=
  model.resolveTreeRange forms words 0 words.size tree

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
