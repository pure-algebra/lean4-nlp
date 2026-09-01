import Nlp.Dependency.Nonprojective
import Nlp.Pipeline.Dependency

/-!
# Effectful nonprojective dependency parsing

The `NLP` facade validates complete documents, applies sentence and arborescence-workspace policy
before inference, observes cancellation between pure kernels, and preserves document order under
bounded quadratic-work scheduling. The existing projective facade remains unchanged.
-/

namespace Nlp.NLP

/-- Apply runtime sentence and workspace policy before nonprojective dependency inference. -/
@[inline] def nonprojectiveDependencySkipReason? (config : Config)
    (tokens : Nat) : Option SkipReason :=
  if config.maxLen < tokens then
    some (.tooLong tokens config.maxLen)
  else
    let entries := Dependency.Arborescence.workspaceEntryCount tokens
    if config.maxChartEntries < entries then
      some (.chartTooLarge entries config.maxChartEntries)
    else
      none

/-- Translate one dynamic score failure without losing its source sentence range. -/
private def nonprojectiveScoreFail (parser : Dependency.Parser)
    (sentence start stop : Nat) (cause : Dependency.ArcScoreError) : Fail :=
  .modelCorrupt parser.diagnosticSource <|
    s!"sentence {sentence} tokens [{start}, {stop}): {arcScoreErrorDetail cause}"

/-- Translate an impossible kernel invariant without losing its source sentence range. -/
private def nonprojectiveKernelFail (parser : Dependency.Parser)
    (sentence start stop : Nat) (cause : Dependency.Arborescence.KernelError) : Fail :=
  .modelCorrupt parser.diagnosticSource <|
    s!"sentence {sentence} tokens [{start}, {stop}): " ++
      s!"nonprojective dependency kernel failed: {reprStr cause}"

/-- Decode one checked document with cancellation between nonprojective sentence kernels. -/
def parseNonprojectiveDependencies (parser : Dependency.Parser) (doc : Doc available)
    (_requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Analysis (Doc (.dep :: available))) := do
  checkCancelled
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause =>
      throw <| Fail.invalidInput "nonprojective dependency parser input"
        s!"semantic validation failed: {repr cause}"
  let ranges := Dependency.Parser.documentRanges checked
  let config := (← read).config
  for range in ranges do
    if let some reason :=
        nonprojectiveDependencySkipReason? config (range.2 - range.1) then
      return .skipped reason
  let kernelConfig : Dependency.Arborescence.KernelConfig := {
    maxWorkspaceEntries := config.maxChartEntries
  }
  let mut results := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    checkCancelled
    let (start, stop) := ranges[sentence]!
    let view ←
      match Dependency.Sentence.ofRange checked.forms checked.pos start stop with
      | .ok value => pure value
      | .error cause =>
        throw <| Fail.invalidInput "nonprojective dependency parser input"
          s!"sentence {sentence} tokens [{start}, {stop}): {repr cause}"
    match parser.parseNonprojectiveWith? kernelConfig view with
    | .ok none => return .noAnalysis
    | .ok (some value) => results := results.push value
    | .error (.scores cause) =>
      throw <| nonprojectiveScoreFail parser sentence start stop cause
    | .error (.kernel (.workspaceBudget required limit)) =>
      return .skipped (.chartTooLarge required limit)
    | .error (.kernel cause) =>
      throw <| nonprojectiveKernelFail parser sentence start stop cause
  checkCancelled
  match Dependency.Parser.assembleNonprojectiveDocument checked results with
  | .ok output => return .ok output
  | .error cause =>
    throw <| .modelCorrupt parser.diagnosticSource <|
      s!"nonprojective dependency extraction violated its checked document invariant: " ++
        reprStr cause

/-- Parse documents with an explicit minimum quadratic-work scheduling unit. -/
@[inline] def parseNonprojectiveDependenciesManyWithMinWork (minWork : Nat)
    (parser : Dependency.Parser) (documents : Array (Doc available))
    (requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Array (Analysis (Doc (.dep :: available)))) :=
  traverseArrayWeightedWithMinWeight minWork documents
    Dependency.Parser.nonprojectiveDocumentWork fun doc ↦
    parseNonprojectiveDependencies parser doc requirements

/-- Parse documents with bounded quadratic-work concurrency and stable input order. -/
@[inline] def parseNonprojectiveDependenciesMany (parser : Dependency.Parser)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Array (Analysis (Doc (.dep :: available)))) :=
  traverseArrayWeighted documents Dependency.Parser.nonprojectiveDocumentWork fun doc ↦
    parseNonprojectiveDependencies parser doc requirements

end Nlp.NLP
