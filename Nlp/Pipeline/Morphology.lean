import Nlp.Morphology
import Nlp.Pipeline.Annotate

/-!
# Functional and effectful morphology APIs

The pure kernel maps a compiled English model over the token/POS columns in one allocation.  The
preferred `NLP` boundary validates inputs, relies on proved output-semantic preservation, retains
typed cancellation, and schedules corpora by token count while preserving input order.
-/

namespace Nlp.Morphology.Model

/-- Lemmatize aligned forms and tags; a missing tag is conservatively classified as `other`. -/
def lemmatizeForms (model : Model) (forms tags : Array String) : Array String :=
  forms.mapIdx fun index surface ↦
    model.lemmaOrSelf (Pos.ofTag (tags.getD index "")) surface

@[simp] theorem lemmatizeForms_size (model : Model) (forms tags : Array String) :
    (model.lemmatizeForms forms tags).size = forms.size := by
  simp [lemmatizeForms]

/-- Pointwise behavior of the allocation-efficient column operation. -/
theorem lemmatizeForms_getElem (model : Model) (forms tags : Array String)
    (index : Nat) (inBounds : index < forms.size) :
    (model.lemmatizeForms forms tags)[index]'(by simpa) =
      model.lemmaOrSelf (Pos.ofTag (tags.getD index "")) (forms[index]'inBounds) := by
  simp [lemmatizeForms]

/-- Add a lemma column after statically requiring aligned token and POS layers. -/
def lemmatizeDoc (model : Model) (doc : Doc available)
    (_requirements : Sub [.tokens, .pos] available := by decide) : Doc (.lemma :: available) :=
  { doc with lemma := model.lemmatizeForms doc.forms doc.pos }

@[simp] theorem lemmatizeDoc_size (model : Model) (doc : Doc available)
    (requirements : Sub [.tokens, .pos] available := by decide) :
    (model.lemmatizeDoc doc requirements).size = doc.size := by
  rfl

@[simp] theorem lemmatizeDoc_lemma_size (model : Model) (doc : Doc available)
    (requirements : Sub [.tokens, .pos] available := by decide) :
    (model.lemmatizeDoc doc requirements).lemma.size = doc.size := by
  simp [lemmatizeDoc, Doc.size]

/-- Pure lemmatization preserves every structural document invariant. -/
theorem lemmatizeDoc_wf (model : Model) (doc : Doc available) (wellFormed : doc.WF)
    (requirements : Sub [.tokens, .pos] available := by decide) :
    (model.lemmatizeDoc doc requirements).WF := by
  rcases wellFormed with ⟨spans, pos, _priorLemma, ner, dep⟩
  refine ⟨spans, ?_, ?_, ?_, ?_⟩
  · simpa [lemmatizeDoc, Doc.size] using pos
  · simp
  · simpa [lemmatizeDoc, Doc.size] using ner
  · simpa [lemmatizeDoc, Doc.size] using dep

/-- Pure lemmatization also preserves token and sentence semantics. -/
theorem lemmatizeDoc_semanticWF (model : Model) (doc : Doc available)
    (semantic : doc.SemanticWF)
    (requirements : Sub [.tokens, .pos] available := by decide) :
    (model.lemmatizeDoc doc requirements).SemanticWF := by
  refine ⟨model.lemmatizeDoc_wf doc semantic.1 requirements, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · intro tokens
    simpa [lemmatizeDoc, Doc.TokenWF, Doc.size] using semantic.2.1 (by simpa using tokens)
  · intro sentences
    have priorSentences : Layer.sents ∈ available := by simpa using sentences
    have prior := semantic.2.2.1 priorSentences
    constructor
    · simpa using prior.1
    · simpa [lemmatizeDoc, Doc.SentenceWF, Doc.size] using prior.2
  · intro dependency
    have priorDependency : Layer.dep ∈ available := by simpa using dependency
    have prior := semantic.2.2.2 priorDependency
    constructor
    · simpa using prior.1
    · simpa [lemmatizeDoc, Doc.DependencyWF] using prior.2

/-- Functional, statically indexed English lemma annotator. -/
def annotator (model : Model) : Ann Id [.tokens, .pos] [.lemma] :=
  Ann.fromPure "lemma" fun requirements doc ↦ model.lemmatizeDoc doc requirements

end Nlp.Morphology.Model

namespace Nlp.NLP

/-- Stable human-readable explanation for pure morphology model failures. -/
def morphologyCompileErrorDetail : Morphology.CompileError → String
  | .emptyLexeme index => s!"lexeme {index} has an empty base form"
  | .emptyExceptionSurface index => s!"exception {index} has an empty surface form"
  | .emptyExceptionLemma index => s!"exception {index} has an empty base form"

/-- Compile caller-supplied lexical data through the typed effectful model boundary. -/
def compileMorphologyModel (lexemes : Array Morphology.Lexeme)
    (exceptions : Array Morphology.ExceptionEntry)
    (source : String := "in-memory English morphology model") : NLP Morphology.Model := do
  checkCancelled
  let model ←
    match Morphology.Model.compile lexemes exceptions with
    | .ok model => pure model
    | .error cause => throw <| .modelCorrupt source (morphologyCompileErrorDetail cause)
  checkCancelled
  return model

private def validateMorphologyInput (doc : Doc available) : NLP (Doc available) :=
  match doc.checkedSemantic with
  | .ok checked => pure checked
  | .error cause =>
      throw <| .invalidInput "lemmatizer input"
        s!"semantic validation failed: {repr cause}"

/-- Lemmatize one checked document through the preferred effectful API. -/
def lemmatize (model : Morphology.Model) (doc : Doc available)
    (requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Doc (.lemma :: available)) := do
  checkCancelled
  let checked ← validateMorphologyInput doc
  let output := model.annotator.run requirements checked
  checkCancelled
  return output

/-- Lemmatize a corpus with token-weighted bounded concurrency and stable order. -/
@[inline] def lemmatizeMany (model : Morphology.Model) (documents : Array (Doc available))
    (requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Array (Doc (.lemma :: available))) :=
  traverseArrayWeighted documents Doc.size fun doc ↦ lemmatize model doc requirements

/-- Lemmatize a corpus with an explicit minimum token weight per scheduling unit. -/
@[inline] def lemmatizeManyWithMinTokens (minTokens : Nat) (model : Morphology.Model)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens, .pos] available := by decide) :
    NLP (Array (Doc (.lemma :: available))) :=
  traverseArrayWeightedWithMinWeight minTokens documents Doc.size fun doc ↦
    lemmatize model doc requirements

end Nlp.NLP
