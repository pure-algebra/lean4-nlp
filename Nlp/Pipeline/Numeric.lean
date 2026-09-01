import Nlp.Normalize.Numeric
import Nlp.Pipeline.Annotate

/-!
# Effectful exact numeric normalization

The functional normalizer remains the reusable kernel. This module checks documents once, applies
runtime sentence-length policy, preserves cooperative cancellation, and exposes stable ordered
corpus traversal through `NLP`.
-/

namespace Nlp.Normalize.Numeric

/-- Token and UTF-8 work used to weight numeric-normalization corpus scheduling. -/
def documentWork (doc : Doc available) : Nat :=
  doc.forms.foldl (fun total form ↦ total + form.utf8ByteSize) doc.size

end Nlp.Normalize.Numeric

namespace Nlp.NLP

private def numericLocation (token : Option Nat := none) : String :=
  match token with
  | some index => s!"numeric normalization token {index}"
  | none => "numeric normalization input"

/-- Find the first sentence-length skip without materializing the sentence-range column. -/
private def numericLengthSkip? (doc : Doc available) (maxLen : Nat) : NLP (Option SkipReason) := do
  if Layer.sents ∈ available then
    let mut start := 0
    for stop in doc.sentEnd do
      checkCancelled
      let tokens := stop - start
      if maxLen < tokens then
        return some (.tooLong tokens maxLen)
      start := stop
  else
    checkCancelled
    if maxLen < doc.size then
      return some (.tooLong doc.size maxLen)
  checkCancelled
  return none

/-- Classify one checked-kernel failure at the effect boundary. -/
private def numericFailure (cause : Normalize.Numeric.Error) :
    NLP (Analysis Normalize.Numeric.Result) := do
  match cause with
  | .tokenBudget _ required limit =>
      return .skipped (.workLimit required limit)
  | .byteBudget _ required limit =>
      return .skipped (.byteLimit required limit)
  | .candidateBudget required limit =>
      return .skipped (.candidateLimit required limit)
  | .mentionBudget required limit =>
      return .skipped (.candidateLimit required limit)
  | .workBudget required limit =>
      return .skipped (.workLimit required limit)
  | .valueDigitBudget _ required limit =>
      return .skipped (.workLimit required limit)
  | .literal _ _ (.byteBudget required limit) =>
      return .skipped (.byteLimit required limit)
  | .literal _ _ (.digitBudget required limit)
  | .literal _ _ (.exponentBudget required limit)
  | .literal _ _ (.valueDigitBudget required limit) =>
      return .skipped (.workLimit required limit)
  | .literal token source literalCause =>
      throw <| .invalidInput (numericLocation (some token))
        s!"strict numeric literal {repr source} failed: {repr literalCause}"
  | .input inputCause =>
      throw <| .modelCorrupt (numericLocation)
        s!"checked numeric kernel repeated semantic validation: {repr inputCause}"
  | .invalidRange ordinal start stop size =>
      throw <| .modelCorrupt (numericLocation)
        s!"checked numeric range {ordinal} escaped bounds: [{start}, {stop}) of {size}"
  | .notSingleExpression start stop =>
      throw <| .modelCorrupt (numericLocation)
        s!"document extraction unexpectedly required one expression in [{start}, {stop})"
  | .outputInvariant =>
      throw <| .modelCorrupt (numericLocation)
        "checked numeric normalization violated its output invariant"

private def normalizeCheckedNumbersWith (config : Normalize.Numeric.Config)
    (doc : Doc available) (semantic : doc.SemanticWF)
    (requirements : Sub [.tokens] available) :
    NLP (Analysis Normalize.Numeric.Result) := do
  checkCancelled
  let runtime := (← read).config
  match ← numericLengthSkip? doc runtime.maxLen with
  | some reason => return .skipped reason
  | none => pure ()
  checkCancelled
  let rangePreflight := Normalize.Numeric.preflightDocumentRangeWorkWith config doc
  checkCancelled
  match rangePreflight with
  | .error cause => return ← numericFailure cause
  | .ok _ => pure ()
  checkCancelled
  let ranges := doc.sentenceRanges
  checkCancelled
  let outcome :=
    Normalize.Numeric.normalizeCheckedDocumentRangesWith config doc semantic ranges rfl
      requirements
  checkCancelled
  match outcome with
  | .ok result => return .ok result
  | .error cause => numericFailure cause

/-- Normalize one checked token document with explicit exact kernel limits. -/
def normalizeNumbersWith (config : Normalize.Numeric.Config) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Analysis Normalize.Numeric.Result) := do
  checkCancelled
  let checkedResult := doc.checkedSemantic
  checkCancelled
  match checked : checkedResult with
  | .ok _ =>
      have semantic : doc.SemanticWF := by
        simp only [checkedResult] at checked
        unfold Doc.checkedSemantic at checked
        split at checked <;> simp_all
      normalizeCheckedNumbersWith config doc semantic requirements
  | .error cause =>
      throw <| .invalidInput (numericLocation)
        s!"semantic validation failed: {repr cause}"

/-- Normalize one document with the production exact-number policy. -/
@[inline] def normalizeNumbers (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Analysis Normalize.Numeric.Result) :=
  normalizeNumbersWith {} doc requirements

/-- Normalize documents with an explicit minimum aggregate scheduling weight. -/
@[inline] def normalizeNumbersManyWithMinWork (minWork : Nat)
    (config : Normalize.Numeric.Config) (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Analysis Normalize.Numeric.Result)) :=
  traverseArrayWeightedWithMinWeight minWork documents Normalize.Numeric.documentWork fun doc ↦
    normalizeNumbersWith config doc requirements

/-- Normalize documents under an explicit policy with stable work-weighted order. -/
@[inline] def normalizeNumbersManyWith (config : Normalize.Numeric.Config)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Analysis Normalize.Numeric.Result)) :=
  traverseArrayWeighted documents Normalize.Numeric.documentWork fun doc ↦
    normalizeNumbersWith config doc requirements

/-- Normalize documents with production limits and stable work-weighted order. -/
@[inline] def normalizeNumbersMany (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Analysis Normalize.Numeric.Result)) :=
  normalizeNumbersManyWith {} documents requirements

end Nlp.NLP
