import Nlp.Dependency.EnglishEnhanced
import Nlp.Pipeline.Annotate

/-!
# Functional and effectful English enhanced dependencies

The functional boundary validates a source document once, enhances sentence ranges without
allocating column slices, and returns proof-carrying alignment between ranges and results. The
preferred `NLP` boundary adds runtime limits, cancellation, and stable work-weighted batching.
-/

namespace Nlp.Dependency.EnglishEnhanced

/-- A complete document failed semantic validation or one sentence enhancement. -/
inductive DocumentError where
  /-- The advertised source layers fail the semantic document boundary. -/
  | input (cause : Doc.SemanticError)
  /-- One exact source sentence range failed the bounded enhancement kernel. -/
  | sentence (index start stop : Nat) (cause : Error)
  /-- Result assembly did not retain exactly one value per selected sentence range. -/
  | resultCount (expected found : Nat)
  deriving Repr

/--
A semantically checked source document and one enhanced result per exact sentence range.

The source remains unchanged. Graph node identifiers restart at one inside every result because
the range kernel consumes sentence-local dependency heads.
-/
structure Document (available : Layers) where
  private mk ::
  /-- The unchanged source document carrying basic dependencies and lexical columns. -/
  source : Doc available
  /-- Exact half-open source token ranges in sentence order. -/
  ranges : Array (Nat × Nat)
  /-- Sentence-local enhanced graphs in the same order as `ranges`. -/
  results : Array Result
  /-- Stored ranges are exactly those advertised by the source document. -/
  ranges_eq : ranges = source.sentenceRanges
  /-- There is exactly one enhanced result for every stored range. -/
  resultCount_eq : results.size = ranges.size
  /-- Source semantic validity is retained at the checked boundary. -/
  sourceSemanticWF : source.SemanticWF

namespace Document

/-- An erased certificate returned after one semantic source check. -/
structure SourceCheck (doc : Doc available) : Type where
  /-- The exact source document satisfies its full advertised semantic boundary. -/
  semantic : doc.SemanticWF

/-- Validate one source document and return its erased semantic proof. -/
def checkSource? (doc : Doc available) : Except Doc.SemanticError (SourceCheck doc) :=
  match checked : doc.checkedSemantic with
  | .error cause => .error cause
  | .ok _ =>
    .ok ⟨by
      by_cases semantic : doc.SemanticWF
      · exact semantic
      · simp [Doc.checkedSemantic, semantic] at checked⟩

/-- Seal aligned sentence results behind the private document-result constructor. -/
def ofResults (source : Doc available) (semantic : source.SemanticWF)
    (results : Array Result) : Except DocumentError (Document available) :=
  let ranges := source.sentenceRanges
  if aligned : results.size = ranges.size then
    .ok ⟨source, ranges, results, rfl, aligned, semantic⟩
  else
    .error (.resultCount ranges.size results.size)

/-- Number of enhanced sentence graphs retained by the document result. -/
@[inline] def sentenceCount (document : Document available) : Nat :=
  document.results.size

/-- Read one exact source range and its aligned enhanced sentence result. -/
def resultAt? (document : Document available) (sentence : Nat) :
    Option ((Nat × Nat) × Result) := do
  let range ← document.ranges[sentence]?
  let result ← document.results[sentence]?
  return (range, result)

end Document

/--
Enhance every selected source sentence under an explicit bounded kernel configuration.

Semantic validation runs once. Each kernel reads its half-open range directly from the aligned
flattened source columns, retaining sentence ordinals and coordinates in typed failures.
-/
def enhanceDocumentWith? (config : Config) (doc : Doc available)
    (_requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    Except DocumentError (Document available) := do
  let sourceCheck ←
    match Document.checkSource? doc with
    | .ok checked => pure checked
    | .error cause => throw <| .input cause
  let ranges := doc.sentenceRanges
  let mut results := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    let (start, stop) := ranges[sentence]!
    let result ←
      match enhanceRangeWith? config doc.head doc.deprel doc.forms doc.lemma doc.pos
          start stop with
      | .ok value => pure value
      | .error cause => throw <| .sentence sentence start stop cause
    results := results.push result
  Document.ofResults doc sourceCheck.semantic results

/-- Enhance every selected source sentence under the production transformer configuration. -/
@[inline] def enhanceDocument? (doc : Doc available)
    (requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    Except DocumentError (Document available) :=
  enhanceDocumentWith? .default doc requirements

/--
Estimate corpus scheduling work from tokens and aligned dependency/lexical UTF-8 bytes.

This is the exact weight used by the default effectful corpus traversal.
-/
def documentWork (doc : Doc available) : Nat :=
  let relationBytes := doc.deprel.foldl (fun total value ↦ total + value.utf8ByteSize) 0
  let formBytes := doc.forms.foldl (fun total value ↦ total + value.utf8ByteSize) 0
  let lemmaBytes := doc.lemma.foldl (fun total value ↦ total + value.utf8ByteSize) 0
  doc.size + relationBytes + formBytes + lemmaBytes

end Nlp.Dependency.EnglishEnhanced

namespace Nlp.NLP

/-- Clamp caller-selected transformer limits against the runtime environment policy. -/
private def clampedEnhancementConfig
    (runtime : Nlp.Config) (requested : Dependency.EnglishEnhanced.Config) :
    Dependency.EnglishEnhanced.Config :=
  { requested with
    maxCandidates := min requested.maxCandidates runtime.maxGraphCandidates
    maxEdges := min requested.maxEdges runtime.maxGraphEdges
    maxLexicalBytes := min requested.maxLexicalBytes runtime.maxGraphLexicalBytes }

/-- Build an exact sentence-coordinate location for effectful invalid-input failures. -/
private def enhancementLocation (sentence start stop : Nat) : String :=
  s!"enhanced dependency input sentence {sentence} tokens [{start}, {stop})"

/-- Translate semantic validation failures while retaining dependency sentence coordinates. -/
private def enhancementSemanticFail (doc : Doc available)
    (cause : Doc.SemanticError) : Fail :=
  match cause with
  | .invalidDependencyDocument (.sentence sentence start stop _) =>
      .invalidInput (enhancementLocation sentence start stop)
        s!"semantic validation failed: {repr cause}"
  | .invalidDependencyTree _ =>
      .invalidInput (enhancementLocation 0 0 doc.size)
        s!"semantic validation failed: {repr cause}"
  | _ =>
      .invalidInput s!"enhanced dependency input tokens [0, {doc.size})"
        s!"semantic validation failed: {repr cause}"

/-- Translate one range-kernel failure with its exact source sentence coordinates. -/
private def enhancementSentenceFail (sentence start stop : Nat)
    (cause : Dependency.EnglishEnhanced.Error) : Fail :=
  .invalidInput (enhancementLocation sentence start stop)
    s!"enhancement failed: {repr cause}"

/--
Enhance one document with runtime policy, typed outcomes, and cooperative cancellation.

Caller limits are clamped against `Env.config`. Length is checked immediately before every
sentence kernel; cancellation is observed between kernels and once before returning the result.
-/
def enhanceDependenciesWith (config : Dependency.EnglishEnhanced.Config)
    (doc : Doc available)
    (_requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    NLP (Analysis (Dependency.EnglishEnhanced.Document available)) := do
  checkCancelled
  let env ← read
  let kernelConfig := clampedEnhancementConfig env.config config
  let sourceCheck ←
    match Dependency.EnglishEnhanced.Document.checkSource? doc with
    | .ok checked => pure checked
    | .error cause => throw <| enhancementSemanticFail doc cause
  let ranges := doc.sentenceRanges
  let mut results := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    checkCancelled
    let (start, stop) := ranges[sentence]!
    let tokens := stop - start
    if env.config.maxLen < tokens then
      return .skipped (.tooLong tokens env.config.maxLen)
    match Dependency.EnglishEnhanced.enhanceRangeWith? kernelConfig doc.head doc.deprel
        doc.forms doc.lemma doc.pos start stop with
    | .ok result => results := results.push result
    | .error (.candidateBudget required limit) =>
        return .skipped (.candidateLimit required limit)
    | .error (.edgeBudget required limit) =>
        return .skipped (.workLimit required limit)
    | .error (.lexicalBudget required limit) =>
        return .skipped (.byteLimit required limit)
    | .error cause => throw <| enhancementSentenceFail sentence start stop cause
  checkCancelled
  match Dependency.EnglishEnhanced.Document.ofResults doc sourceCheck.semantic results with
  | .ok document => return .ok document
  | .error cause =>
      throw <| .invalidInput "enhanced dependency result assembly" (reprStr cause)

/-- Enhance one document with the production transformer and runtime environment policy. -/
@[inline] def enhanceDependencies (doc : Doc available)
    (requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    NLP (Analysis (Dependency.EnglishEnhanced.Document available)) :=
  enhanceDependenciesWith .default doc requirements

/-- Enhance documents with an explicit minimum aggregate-token scheduling unit. -/
@[inline] def enhanceDependenciesManyWithMinTokens (minTokens : Nat)
    (config : Dependency.EnglishEnhanced.Config) (documents : Array (Doc available))
    (requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    NLP (Array (Analysis (Dependency.EnglishEnhanced.Document available))) :=
  traverseArrayWeightedWithMinWeight minTokens documents Doc.size fun doc ↦
    enhanceDependenciesWith config doc requirements

/-- Enhance documents with an explicit minimum aggregate lexical-work scheduling unit. -/
@[inline] def enhanceDependenciesManyWithMinWork (minWork : Nat)
    (config : Dependency.EnglishEnhanced.Config) (documents : Array (Doc available))
    (requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    NLP (Array (Analysis (Dependency.EnglishEnhanced.Document available))) :=
  traverseArrayWeightedWithMinWeight minWork documents
      Dependency.EnglishEnhanced.documentWork fun doc ↦
    enhanceDependenciesWith config doc requirements

/-- Enhance documents under an explicit transformer policy with stable lexical-work order. -/
@[inline] def enhanceDependenciesManyWith (config : Dependency.EnglishEnhanced.Config)
    (documents : Array (Doc available))
    (requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    NLP (Array (Analysis (Dependency.EnglishEnhanced.Document available))) :=
  traverseArrayWeighted documents Dependency.EnglishEnhanced.documentWork fun doc ↦
    enhanceDependenciesWith config doc requirements

/-- Enhance documents under production transformer policy with stable lexical-work order. -/
@[inline] def enhanceDependenciesMany (documents : Array (Doc available))
    (requirements : Sub [.dep, .lemma, .pos, .tokens] available := by decide) :
    NLP (Array (Analysis (Dependency.EnglishEnhanced.Document available))) :=
  enhanceDependenciesManyWith .default documents requirements

end Nlp.NLP
