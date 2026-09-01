import Nlp.Dependency.Parser
import Nlp.Pipeline.Annotate

/-!
# Functional and effectful projective dependency parsing

The functional bridge parses checked form/POS sentence views and writes sentence-local CoNLL-U
heads into `Doc`. The preferred `NLP` facade validates inputs, applies sentence and chart policy
before allocation, observes cancellation between sentences, and schedules document batches by
cubic parsing work while preserving order.
-/

namespace Nlp.Dependency.Parser

/-- A checked document could not be converted into projective dependency output. -/
inductive DocumentError where
  | input (cause : Doc.SemanticError)
  | sentenceView (sentence start stop : Nat) (cause : SentenceError)
  | scores (sentence start stop : Nat) (cause : ArcScoreError)
  | sentenceCount (expected found : Nat)
  | resultSize (sentence expected heads relations : Nat)
  | output (cause : Doc.SemanticError)
  deriving Repr

/-- Half-open flattened sentence ranges selected by a document's advertised layers. -/
def documentRanges (doc : Doc available) : Array (Nat × Nat) :=
  doc.sentenceRanges

/-- Cubic scheduling work implied by one checked document's sentence ranges. -/
def documentWork (doc : Doc available) : Nat :=
  doc.sentenceCubicWork

/-- Append one aligned local result, retaining its sentence ordinal in invariant failures. -/
private def appendResult (sentence expected : Nat) (result : Eisner.NamedResult)
    (heads : Array Nat) (relations : Array String) :
    Except DocumentError (Array Nat × Array String) := do
  if result.heads.size != expected || result.relations.size != expected then
    throw <| .resultSize sentence expected result.heads.size result.relations.size
  return (heads ++ result.heads, relations ++ result.relations)

/-- Validate and assemble exact sentence-local heads into a document. -/
def assembleDocument (doc : Doc available) (results : Array Eisner.NamedResult) :
    Except DocumentError (Doc (.dep :: available)) := do
  let ranges := documentRanges doc
  if results.size != ranges.size then
    throw <| .sentenceCount ranges.size results.size
  let mut heads : Array Nat := #[]
  let mut relations : Array String := #[]
  for sentence in [0:ranges.size] do
    let range := ranges[sentence]!
    let result := results[sentence]!
    let appended ← appendResult sentence (range.2 - range.1) result heads relations
    heads := appended.1
    relations := appended.2
  let output : Doc (.dep :: available) := { doc with head := heads, deprel := relations }
  match output.checkedSemantic with
  | .ok checked => pure checked
  | .error cause => throw <| .output cause

/--
Parse every advertised sentence through the pure functional API.

The first sentence without a finite projective analysis makes the document result `none`.
-/
def parseDocument? (parser : Parser) (doc : Doc available)
    (_requirements : Sub [.tokens, .pos] available := by decide) :
    Except DocumentError (Option (Doc (.dep :: available))) := do
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause => throw <| .input cause
  let ranges := documentRanges checked
  let mut results := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    let (start, stop) := ranges[sentence]!
    let view ←
      match Sentence.ofRange checked.forms checked.pos start stop with
      | .ok value => pure value
      | .error cause => throw <| .sentenceView sentence start stop cause
    let result ←
      match parser.parse? view with
      | .ok value => pure value
      | .error cause => throw <| .scores sentence start stop cause
    match result with
    | none => return none
    | some value => results := results.push value
  return some (← assembleDocument checked results)

end Nlp.Dependency.Parser

namespace Nlp.NLP

/-- Stable rendering for sentence-score compilation failures. -/
def arcScoreErrorDetail : Dependency.ArcScoreError → String
  | .tokenCapacity count =>
      s!"token count {count} leaves no UInt32 split or dependency identifier"
  | .tokenBudget required limit =>
      s!"arc scoring needs {required} tokens but the model limit is {limit}"
  | .relationCapacity count =>
      s!"relation inventory {count} exceeds the UInt32 identifier capacity"
  | .relationBudget required limit =>
      s!"arc scoring needs {required} relations but the model limit is {limit}"
  | .zeroRelations => "dependency relation inventory is empty"
  | .invalidRootRelation root relations =>
      s!"root relation {root} is outside the relation range [0, {relations})"
  | .emptyRelationName index => s!"dependency relation name {index} is empty"
  | .duplicateRelationName first duplicate name =>
      s!"dependency relation {duplicate} duplicates relation {first}: {repr name}"
  | .arcEntryBudget required limit =>
      s!"compiled arc table needs {required} entries but the model limit is {limit}"
  | .scoreVisitBudget required limit =>
      s!"arc compilation needs {required} labeled visits but the model limit is {limit}"
  | .denseScoreBudget required limit =>
      s!"dense score input needs {required} entries but the model limit is {limit}"
  | .denseDimension expected found =>
      s!"dense arc-score dimensions disagree: expected {expected}, found {found}"
  | .invalidCost head dependent relation value bits =>
      s!"arc score head={head} dependent={dependent} relation={relation} is " ++
        s!"{reprStr value} (IEEE-754 bits={bits}); expected a finite nonnegative value, " ++
        "canonical positive zero, or positive infinity to forbid the candidate"

/-- Compile a reusable dependency parser through the typed effectful model boundary. -/
def compileDependencyParserWith (config : Dependency.ArcScoreConfig)
    (relationNames : Array String) (rootRelation : Nat) (scorer : Dependency.Scorer)
    (source : String := "in-memory dependency scorer") : NLP Dependency.Parser := do
  checkCancelled
  let parser ←
    match Dependency.Parser.compileWith config relationNames rootRelation scorer with
    | .ok value => pure (value.withDiagnosticSource source)
    | .error cause => throw <| .modelCorrupt source (arcScoreErrorDetail cause)
  checkCancelled
  return parser

/-- Compile a reusable dependency parser under production score-compilation limits. -/
@[inline] def compileDependencyParser (relationNames : Array String) (rootRelation : Nat)
    (scorer : Dependency.Scorer) (source : String := "in-memory dependency scorer") :
    NLP Dependency.Parser :=
  compileDependencyParserWith .default relationNames rootRelation scorer source

/-- Apply runtime sentence and chart allocation policy before dependency inference. -/
@[inline] def dependencySkipReason? (config : Config) (tokens : Nat) : Option SkipReason :=
  if config.maxLen < tokens then
    some (.tooLong tokens config.maxLen)
  else
    let entries := Dependency.Eisner.chartEntryCount tokens
    if config.maxChartEntries < entries then
      some (.chartTooLarge entries config.maxChartEntries)
    else
      none

/-- Translate one dynamic score failure without losing its sentence range. -/
private def dependencyScoreFail (parser : Dependency.Parser) (sentence start stop : Nat)
    (cause : Dependency.ArcScoreError) : Fail :=
  .modelCorrupt parser.diagnosticSource <|
    s!"sentence {sentence} tokens [{start}, {stop}): {arcScoreErrorDetail cause}"

/-- Parse one checked document with cancellation between sentence kernels. -/
def parseDependencies (parser : Dependency.Parser) (doc : Doc available)
    (_requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Analysis (Doc (.dep :: available))) := do
  checkCancelled
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause =>
      throw <| Fail.invalidInput "dependency parser input"
        s!"semantic validation failed: {repr cause}"
  let ranges := Dependency.Parser.documentRanges checked
  let config := (← read).config
  for range in ranges do
    if let some reason := dependencySkipReason? config (range.2 - range.1) then
      return .skipped reason
  let mut results := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    checkCancelled
    let (start, stop) := ranges[sentence]!
    let view ←
      match Dependency.Sentence.ofRange checked.forms checked.pos start stop with
      | .ok value => pure value
      | .error cause =>
        throw <| Fail.invalidInput "dependency parser input"
          s!"sentence {sentence} tokens [{start}, {stop}): {repr cause}"
    let result ←
      match parser.parse? view with
      | .ok value => pure value
      | .error cause => throw <| dependencyScoreFail parser sentence start stop cause
    match result with
    | none => return .noAnalysis
    | some value => results := results.push value
  checkCancelled
  match Dependency.Parser.assembleDocument checked results with
  | Except.ok output => return Analysis.ok output
  | Except.error cause =>
    throw <| .modelCorrupt parser.diagnosticSource
      s!"dependency extraction violated its checked document invariant: {repr cause}"

/-- Parse documents with an explicit minimum cubic-work scheduling unit. -/
@[inline] def parseDependenciesManyWithMinWork (minWork : Nat)
    (parser : Dependency.Parser) (documents : Array (Doc available))
    (requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Array (Analysis (Doc (.dep :: available)))) :=
  traverseArrayWeightedWithMinWeight minWork documents
    Dependency.Parser.documentWork fun doc =>
    parseDependencies parser doc requirements

/-- Parse documents with bounded, cubic-work-balanced concurrency and stable order. -/
@[inline] def parseDependenciesMany (parser : Dependency.Parser)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Array (Analysis (Doc (.dep :: available)))) :=
  traverseArrayWeighted documents Dependency.Parser.documentWork fun doc =>
    parseDependencies parser doc requirements

end Nlp.NLP
