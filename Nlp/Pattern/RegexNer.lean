import Nlp.Pattern.Automaton
import Nlp.Pattern.Phrase
import Nlp.Pattern.Token

/-!
# Typed regular-expression named-entity rules

This module compiles ordered named-entity rules into separate Thompson and exact-phrase lanes,
then arbitrates their full-column matches with one deterministic policy. Higher priority wins,
followed by greater span width and lower source-rule ordinal. Matching is sentence-local and never
allocates a token slice. Existing non-background entity runs are changed only when a rule names
their label as overwriteable and covers each run without splitting either boundary.

The regular lane is a typed, first-order subset over `TokenAtom`. It deliberately does not claim
Stanford TokensRegex's full textual DSL, capture groups, actions, or arbitrary annotation access.
-/

namespace Nlp.Pattern

/-- The two supported RegexNER pattern representations. -/
inductive RegexNerPattern where
  /-- A typed regular language over token-column predicates. -/
  | regular (pattern : Regular TokenAtom)
  /-- An exact, case-sensitive sequence of source-preserving token forms. -/
  | phrase (forms : Array String)
  deriving Repr, DecidableEq

/-- One ordered RegexNER source rule before bounded compilation. -/
structure RegexNerRule where
  /-- Pattern matched independently inside each advertised sentence range. -/
  pattern : RegexNerPattern
  /-- Nonempty flat entity class other than reserved background `O`. -/
  entityClass : String
  /-- Finite precedence score; larger values win overlapping conflicts. -/
  priority : Float := 0.0
  /-- Existing non-background classes this rule may replace as complete runs. -/
  overwriteable : Array String := #[]
  deriving Repr

/-- Independent resource policies for the regular and exact-phrase compiler lanes. -/
structure RegexNerCompileConfig where
  /-- Thompson-NFA allocation policy. -/
  regular : CompileConfig := {}
  /-- Bounded overlapping-search policy retained by the compiled model. -/
  search : SearchConfig := { maxWork := 16_777_216, maxMatches := 65_536 }
  /-- Exact-phrase trie allocation policy. -/
  phrase : PhraseCompileConfig := {}
  /-- Maximum number of mixed-lane source rules and retained metadata records. -/
  maxRules : Nat := 65_536
  /-- Maximum aggregate number of pattern, predicate, token, and overwrite entries. -/
  maxPayloadEntries : Nat := 1_048_576
  /-- Maximum aggregate UTF-8 bytes referenced by source rule strings. -/
  maxSourceBytes : Nat := 67_108_864
  deriving Repr, DecidableEq, Inhabited

/-- Why ordered RegexNER rules could not form a validated two-lane model. -/
inductive RegexNerCompileError where
  /-- The mixed source array exceeded the configured rule budget. -/
  | ruleBudget (required limit : Nat)
  /-- Aggregate source structure exceeded the configured entry budget. -/
  | payloadBudget (required limit : Nat)
  /-- Aggregate source strings exceeded the configured UTF-8 byte budget. -/
  | sourceByteBudget (required limit : Nat)
  /-- A source rule has no output entity class. -/
  | emptyEntity (rule : Nat)
  /-- A source rule tries to emit the reserved background class. -/
  | reservedEntity (rule : Nat)
  /-- A source priority is NaN or infinite; exact bits are retained for diagnostics. -/
  | invalidPriority (rule : Nat) (value : Float) (bits : UInt64)
  /-- An exact-phrase source rule has no tokens. -/
  | emptyPhrase (rule : Nat)
  /-- An exact-phrase source token is empty. -/
  | emptyPhraseToken (rule token : Nat)
  /-- Bounded Thompson compilation failed. -/
  | regular (cause : CompileError)
  /-- Bounded exact-phrase compilation failed. -/
  | phrase (cause : PhraseCompileError)
  deriving Repr

/-- Compiler lane used by a defensive model-consistency diagnostic. -/
inductive RegexNerLane where
  /-- The typed Thompson-NFA lane. -/
  | regular
  /-- The exact-phrase trie lane. -/
  | phrase
  deriving Repr, DecidableEq, Inhabited

/-- Why a RegexNER model could not produce a checked aligned document. -/
inductive RegexNerDocumentError where
  /-- The input document failed semantic boundary validation. -/
  | input (cause : Doc.SemanticError)
  /-- The document's phantom index omits a column read by a compiled token atom. -/
  | missingLayer (layer : Layer)
  /-- A compiled match exposed a lane ordinal outside its private metadata table. -/
  | invalidLaneRule (lane : RegexNerLane) (rule available : Nat)
  /-- A mutable-by-value class column is not aligned with the checked token column. -/
  | classAlignment (expected found : Nat)
  /-- Conservative overlapping-NFA work exceeded the model's retained search policy. -/
  | searchWorkBudget (required limit : Nat)
  /-- Combined regular and phrase candidates exceeded the retained range policy. -/
  | candidateBudget (required limit : Nat)
  /-- An overlapping search returned an error impossible for its selected mode. -/
  | invalidRegularSearch (nullableRules : Array Nat)
  /-- The rewritten output violated the semantic document boundary. -/
  | output (cause : Doc.SemanticError)
  deriving Repr

/-- Immutable source metadata stored parallel to one private compiler lane. -/
private structure CompiledRule where
  /-- Original ordinal in the caller's mixed-lane rule array. -/
  source : Nat
  /-- Flat output class. -/
  entityClass : String
  /-- Validated finite precedence. -/
  priority : Float
  /-- Existing non-background labels this source rule may replace. -/
  overwriteable : Array String

/-- A validated, constructor-protected RegexNER model with two immutable matching lanes. -/
structure RegexNerModel where
  private mk ::
  /-- Compiled regular-pattern lane. -/
  private regularAutomaton : Automaton TokenAtom
  /-- Metadata parallel to regular source ordinals. -/
  private regularRules : Array CompiledRule
  /-- Compiled exact-phrase lane. -/
  private phraseAutomaton : PhraseAutomaton
  /-- Metadata parallel to phrase source ordinals. -/
  private phraseRules : Array CompiledRule
  /-- Total number of mixed-lane source rules. -/
  private sourceRuleCount : Nat
  /-- Runtime work and combined candidate policy. -/
  private search : SearchConfig
  /-- Stable, duplicate-free annotation columns read during matching. -/
  private requirements : Layers
  /-- Caller-selected identity retained by effectful diagnostics. -/
  private source : String

/--
A semantically checked document branded with the exact model that validated its dynamic layers.

The constructor is private, so public range rewriting cannot bypass `validateDocument` or use a
session produced by a different model.
-/
structure RegexNerSession (available : Layers) where
  private mk ::
  /-- Model whose dynamic token-atom requirements were checked. -/
  private model : RegexNerModel
  /-- Semantically checked source document. -/
  private doc : Doc available

namespace RegexNerSession

/-- Semantically checked source document retained by a validated session. -/
@[inline] def document (session : RegexNerSession available) : Doc available :=
  session.doc

/-- Sentence ranges selected by the checked document's advertised layers. -/
@[inline] def sentenceRanges (session : RegexNerSession available) : Array (Nat × Nat) :=
  session.doc.sentenceRanges

end RegexNerSession

namespace RegexNerModel

/-- Insert one annotation requirement exactly once. -/
private def insertLayer (layers : Layers) (layer : Layer) : Layers :=
  if layer ∈ layers then layers else layers ++ [layer]

/-- Stable union for the small annotation-layer universe. -/
private def unionLayers (left right : Layers) : Layers :=
  right.foldl insertLayer left

/-- Collect every annotation layer read by a typed regular pattern. -/
private def regularRequiredLayers : Regular TokenAtom → Layers
  | .empty | .epsilon => []
  | .atom atom => atom.requiredLayers
  | .alt left right | .seq left right =>
      unionLayers (regularRequiredLayers left) (regularRequiredLayers right)
  | .star body => regularRequiredLayers body

/-- Aggregate retained source structure and referenced UTF-8 bytes. -/
private structure SourceMeasure where
  entries : Nat := 0
  bytes : Nat := 0

/-- Add independent source-resource measures. -/
@[inline] private def SourceMeasure.add (left right : SourceMeasure) : SourceMeasure :=
  ⟨left.entries + right.entries, left.bytes + right.bytes⟩

/-- Measure a retained string array without copying it. -/
private def stringArrayMeasure (values : Array String) : SourceMeasure :=
  values.foldl (init := ⟨values.size, 0⟩) fun measure value ↦
    { measure with bytes := measure.bytes + value.utf8ByteSize }

/-- Measure one first-order text predicate and its referenced strings. -/
private def textTestMeasure : TextTest → SourceMeasure
  | .any => ⟨1, 0⟩
  | .equal value | .prefix value | .suffix value => ⟨2, value.utf8ByteSize⟩
  | .oneOf values => (⟨1, 0⟩ : SourceMeasure).add (stringArrayMeasure values)

/-- Measure one recursively composed token predicate. -/
private def tokenAtomMeasure : TokenAtom → SourceMeasure
  | .form test | .pos test | .lemma test | .ner test =>
      (⟨1, 0⟩ : SourceMeasure).add (textTestMeasure test)
  | .both left right | .either left right =>
      ((⟨1, 0⟩ : SourceMeasure).add (tokenAtomMeasure left)).add
        (tokenAtomMeasure right)
  | .negate atom => (⟨1, 0⟩ : SourceMeasure).add (tokenAtomMeasure atom)

/-- Measure one regular-pattern syntax tree and its token predicates. -/
private def regularMeasure : Regular TokenAtom → SourceMeasure
  | .empty | .epsilon => ⟨1, 0⟩
  | .atom atom => (⟨1, 0⟩ : SourceMeasure).add (tokenAtomMeasure atom)
  | .alt left right | .seq left right =>
      ((⟨1, 0⟩ : SourceMeasure).add (regularMeasure left)).add
        (regularMeasure right)
  | .star body => (⟨1, 0⟩ : SourceMeasure).add (regularMeasure body)

/-- Measure metadata, pattern payload, and retained strings for one source rule. -/
private def ruleMeasure (rule : RegexNerRule) : SourceMeasure :=
  let metadata : SourceMeasure := ⟨1, rule.entityClass.utf8ByteSize⟩
  let overwriteable := stringArrayMeasure rule.overwriteable
  let pattern := match rule.pattern with
    | .regular regular => regularMeasure regular
    | .phrase forms => (⟨1, 0⟩ : SourceMeasure).add (stringArrayMeasure forms)
  (metadata.add overwriteable).add pattern

/-- Validate one source rule before any lane-specific allocation occurs. -/
private def validateRule (source : Nat) (rule : RegexNerRule) :
    Except RegexNerCompileError Unit := do
  if rule.entityClass.isEmpty then
    throw <| .emptyEntity source
  if rule.entityClass == "O" then
    throw <| .reservedEntity source
  unless rule.priority.isFinite do
    throw <| .invalidPriority source rule.priority rule.priority.toBits
  match rule.pattern with
  | .regular _ => pure ()
  | .phrase forms =>
      if forms.isEmpty then
        throw <| .emptyPhrase source
      for token in [0:forms.size] do
        if forms[token]!.isEmpty then
          throw <| .emptyPhraseToken source token

/-- Retain the source fields needed after the pattern itself has been compiled. -/
@[inline] private def compileMetadata (source : Nat) (rule : RegexNerRule) : CompiledRule :=
  ⟨source, rule.entityClass, rule.priority, rule.overwriteable⟩

/--
Compile ordered mixed-lane rules under explicit resource policies.

Validation and lane construction preserve the original source ordinal even though regular and
exact-phrase patterns compile into separate immutable machines.
-/
def compileWith (config : RegexNerCompileConfig) (rules : Array RegexNerRule) :
    Except RegexNerCompileError RegexNerModel := do
  if config.maxRules < rules.size then
    throw <| .ruleBudget rules.size config.maxRules
  let mut measure : SourceMeasure := {}
  let mut validationSource := 0
  for rule in rules do
    validateRule validationSource rule
    measure := measure.add (ruleMeasure rule)
    validationSource := validationSource + 1
  if config.maxPayloadEntries < measure.entries then
    throw <| .payloadBudget measure.entries config.maxPayloadEntries
  if config.maxSourceBytes < measure.bytes then
    throw <| .sourceByteBudget measure.bytes config.maxSourceBytes
  let mut regularPatterns : Array (Regular TokenAtom) := #[]
  let mut regularRules : Array CompiledRule := #[]
  let mut phrases : Array (Array String) := #[]
  let mut phraseRules : Array CompiledRule := #[]
  let mut requirements : Layers := [.tokens]
  let mut source := 0
  for rule in rules do
    match rule.pattern with
    | .regular pattern =>
        regularPatterns := regularPatterns.push pattern
        regularRules := regularRules.push (compileMetadata source rule)
        requirements := unionLayers requirements (regularRequiredLayers pattern)
    | .phrase forms =>
        phrases := phrases.push forms
        phraseRules := phraseRules.push (compileMetadata source rule)
    source := source + 1
  let regularAutomaton ←
    match Automaton.compileWith config.regular regularPatterns with
    | .ok value => pure value
    | .error cause => throw <| RegexNerCompileError.regular cause
  let phraseAutomaton ←
    match PhraseAutomaton.compile phrases config.phrase with
    | .ok value => pure value
    | .error cause => throw <| RegexNerCompileError.phrase cause
  return .mk regularAutomaton regularRules phraseAutomaton phraseRules rules.size config.search
    requirements "in-memory RegexNER rules"

/-- Compile ordered mixed-lane rules with the default resource policies. -/
@[inline] def compile (rules : Array RegexNerRule) :
    Except RegexNerCompileError RegexNerModel :=
  compileWith {} rules

/-- Replace only the caller-facing identity retained for effectful diagnostics. -/
def withDiagnosticSource (model : RegexNerModel) (source : String) : RegexNerModel :=
  .mk model.regularAutomaton model.regularRules model.phraseAutomaton model.phraseRules
    model.sourceRuleCount model.search model.requirements source

/-- Caller-facing identity retained for effectful diagnostics. -/
@[inline] def diagnosticSource (model : RegexNerModel) : String :=
  model.source

/-- Stable, duplicate-free annotation layers read by the compiled token predicates. -/
@[inline] def requiredLayers (model : RegexNerModel) : Layers :=
  model.requirements

/-- Number of original mixed-lane source rules retained by the model. -/
@[inline] def ruleCount (model : RegexNerModel) : Nat :=
  model.sourceRuleCount

/-- Validate document semantics and every dynamically required annotation layer exactly once. -/
def validateDocument (model : RegexNerModel) (doc : Doc available)
    (_requirements : Sub [.tokens] available := by decide) :
    Except RegexNerDocumentError (RegexNerSession available) := do
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause => throw <| .input cause
  for layer in model.requirements do
    unless decide (layer ∈ available) do
      throw <| .missingLayer layer
  return .mk model checked

/--
Select the mutable-by-value starting class column after document validation.

An advertised, aligned NER column is preserved. Otherwise one background `O` is synthesized per
token, so unadvertised stale storage never affects matching or overwrite protection.
-/
def initialClasses (session : RegexNerSession available) : Array String :=
  if decide (Layer.ner ∈ available) && session.doc.ner.size == session.doc.size then
    session.doc.ner
  else
    Array.replicate session.doc.size "O"

/-- One normalized candidate carrying its original mixed-lane rule identity. -/
private structure Candidate where
  /-- Validated rule metadata. -/
  rule : CompiledRule
  /-- Inclusive absolute token position. -/
  start : Nat
  /-- Exclusive absolute token position. -/
  stop : Nat

namespace Candidate

/-- Token width of one nonempty candidate. -/
@[inline] private def width (candidate : Candidate) : Nat :=
  candidate.stop - candidate.start

/--
Total deterministic precedence used before conflict filtering.

Higher finite priority wins, then longer width, then lower mixed-lane source ordinal. Exact
remaining ties use lower start and stop coordinates.
-/
private def precedes (left right : Candidate) : Bool :=
  if decide (right.rule.priority < left.rule.priority) then
    true
  else if decide (left.rule.priority < right.rule.priority) then
    false
  else if right.width < left.width then
    true
  else if left.width < right.width then
    false
  else if left.rule.source < right.rule.source then
    true
  else if right.rule.source < left.rule.source then
    false
  else if left.start < right.start then
    true
  else if right.start < left.start then
    false
  else
    decide (left.stop ≤ right.stop)

end Candidate

/-- Map one regular-lane match back to its original source metadata. -/
private def regularCandidate (model : RegexNerModel) (matched : Match) :
    Except RegexNerDocumentError Candidate :=
  match model.regularRules[matched.rule]? with
  | some rule => .ok ⟨rule, matched.start, matched.stop⟩
  | none => .error <| .invalidLaneRule .regular matched.rule model.regularRules.size

/-- Map one exact-phrase match back to its original source metadata. -/
private def phraseCandidate (model : RegexNerModel) (matched : PhraseMatch) :
    Except RegexNerDocumentError Candidate :=
  match model.phraseRules[matched.rule]? with
  | some rule => .ok ⟨rule, matched.start, matched.stop⟩
  | none => .error <| .invalidLaneRule .phrase matched.rule model.phraseRules.size

/-- Collect both matching lanes over one normalized full-column range without token slices. -/
private def candidatesRange (session : RegexNerSession available)
    (range : Range) : Except RegexNerDocumentError (Array Candidate) := do
  let model := session.model
  let doc := session.doc
  let regular ← if model.regularRules.isEmpty then pure #[] else
    match model.regularAutomaton.findOverlappingRangeWith model.search
        (TokenAtom.holdsAtUnchecked doc) doc.size range.start range.stop with
    | .ok found => pure found
    | .error (.workBudget required limit) =>
        throw <| .searchWorkBudget required limit
    | .error (.matchBudget required limit) =>
        throw <| .candidateBudget required limit
    | .error (.nullableRules rules) => throw <| .invalidRegularSearch rules
  let mut candidates := Array.emptyWithCapacity regular.size
  for matched in regular do
    candidates := candidates.push (← model.regularCandidate matched)
  let remaining := model.search.maxMatches - candidates.size
  let phrases ← if model.phraseRules.isEmpty then pure #[] else
    match model.phraseAutomaton.findAllRangeWithLimit remaining doc.forms
        range.start range.stop with
    | .ok found => pure found
    | .error (.matchBudget required _) =>
        throw <| .candidateBudget (candidates.size + required) model.search.maxMatches
  for matched in phrases do
    candidates := candidates.push (← model.phraseCandidate matched)
  return candidates

/-- Whether any token in one absolute span is already claimed during this range rewrite. -/
private def spanOccupied (occupied : Array Bool) (lower start stop : Nat) : Bool := Id.run do
  for position in [start:stop] do
    if occupied.getD (position - lower) false then
      return true
  return false

/-- Whether one existing class is background or explicitly replaceable by a source rule. -/
@[inline] private def labelOverwriteable (rule : CompiledRule) (label : String) : Bool :=
  label == "O" || rule.overwriteable.contains label

/-- Whether a rule may replace every existing class across a complete candidate span. -/
private def spanOverwriteable (rule : CompiledRule) (existing : Array String)
    (start stop : Nat) : Bool := Id.run do
  for position in [start:stop] do
    unless labelOverwriteable rule (existing.getD position "") do
      return false
  return true

/-- Whether a candidate's left boundary cuts a range-local non-background entity run. -/
private def splitsLeftBoundary (existing : Array String) (lower start : Nat) : Bool :=
  if start ≤ lower then
    false
  else
    let current := existing.getD start ""
    current != "O" && current == existing.getD (start - 1) ""

/-- Whether a candidate's right boundary cuts a range-local non-background entity run. -/
private def splitsRightBoundary (existing : Array String) (upper stop : Nat) : Bool :=
  if stop = 0 || upper ≤ stop then
    false
  else
    let current := existing.getD (stop - 1) ""
    current != "O" && current == existing.getD stop ""

/-- Decide whether one candidate can be selected as a complete, nonconflicting rewrite. -/
private def canSelect (range : Range) (existing : Array String) (occupied : Array Bool)
    (candidate : Candidate) : Bool :=
  decide (range.start ≤ candidate.start) && decide (candidate.start < candidate.stop) &&
    decide (candidate.stop ≤ range.stop) &&
    !spanOccupied occupied range.start candidate.start candidate.stop &&
    !splitsLeftBoundary existing range.start candidate.start &&
    !splitsRightBoundary existing range.stop candidate.stop &&
    spanOverwriteable candidate.rule existing candidate.start candidate.stop

/-- Mark one selected candidate in a range-local occupancy array. -/
private def claimCandidate (range : Range) (occupied : Array Bool)
    (candidate : Candidate) : Array Bool := Id.run do
  let mut claimed := occupied
  for position in [candidate.start:candidate.stop] do
    claimed := claimed.set! (position - range.start) true
  return claimed

/-- Select complete nonconflicting candidates without retaining an alias during class writes. -/
private def selectCandidates (range : Range) (existing : Array String)
    (ordered : Array Candidate) : Array Candidate := Id.run do
  let mut selected := Array.emptyWithCapacity ordered.size
  let mut occupied := Array.replicate range.width false
  for candidate in ordered do
    if canSelect range existing occupied candidate then
      selected := selected.push candidate
      occupied := claimCandidate range occupied candidate
  return selected

/-- Rewrite every selected, disjoint span after read-only conflict selection has finished. -/
private def applyCandidates (classes : Array String) (selected : Array Candidate) :
    Array String := Id.run do
  let mut output := classes
  for candidate in selected do
    for position in [candidate.start:candidate.stop] do
      output := output.set! position candidate.rule.entityClass
  return output

/--
Rewrite one normalized sentence range of a validated document.

The caller should first cross `validateDocument`, then thread the returned class array through
successive ranges. This kernel does not repeat document or required-layer validation. It checks
class alignment, matches both lanes without slices, and rewrites only complete selected spans.
-/
def rewriteRange (session : RegexNerSession available) (classes : Array String)
    (start stop : Nat) :
    Except RegexNerDocumentError (Array String) := do
  if classes.size != session.doc.size then
    throw <| .classAlignment session.doc.size classes.size
  let range := normalizeRange session.doc.size start stop
  let candidates ← candidatesRange session range
  let ordered := candidates.mergeSort Candidate.precedes
  let selected := selectCandidates range classes ordered
  return applyCandidates classes selected

/-- Build and semantically validate a final `.ner` document from an aligned class column. -/
def assembleDocument (session : RegexNerSession available) (classes : Array String) :
    Except RegexNerDocumentError (Doc (.ner :: available)) := do
  if classes.size != session.doc.size then
    throw <| .classAlignment session.doc.size classes.size
  let output : Doc (.ner :: available) := { session.doc with ner := classes }
  match output.checkedSemantic with
  | .ok value => pure value
  | .error cause => throw <| .output cause

/--
Apply RegexNER rules through the pure checked document API.

Advertised sentences are independent matching ranges. A token-only document is one range, while
an empty token document has none. This function uses the same range seam exposed to effectful
callers for cancellation and sentence-length checks between kernels.
-/
def tagDocument (model : RegexNerModel) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    Except RegexNerDocumentError (Doc (.ner :: available)) := do
  let checked ← model.validateDocument doc requirements
  let mut classes := initialClasses checked
  for range in checked.sentenceRanges do
    classes ← rewriteRange checked classes range.1 range.2
  assembleDocument checked classes

end RegexNerModel

end Nlp.Pattern
