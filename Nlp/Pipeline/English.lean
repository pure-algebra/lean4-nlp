import Nlp.Pipeline.Morphology
import Nlp.Pipeline.Pos
import Nlp.Pipeline.Tokenize

/-!
# Fused English analysis

The pure kernel adds POS and lemma columns in one statically indexed composition. The preferred
`NLP` boundary checks each input once, retains cooperative cancellation, and schedules corpora by
token or UTF-8 byte weight without changing their order.
-/

namespace Nlp.English

/-- Supply token and newly produced POS layers to the morphology stage. -/
private theorem morphologyRequirements {available : Layers}
    (requirements : Sub [.tokens] available) :
    Sub [.tokens, .pos] (.pos :: available) := by
  intro layer present
  have classified : layer = .tokens ∨ layer = .pos := by simpa using present
  rcases classified with rfl | rfl
  · exact List.Mem.tail .pos (requirements .tokens (by simp))
  · exact List.Mem.head available

/-- Tag a token document and lemmatize it from the newly produced POS column. -/
def tagAndLemmatizeDoc (tagger : Sequence.PosTagger) (morphology : Morphology.Model)
    (doc : Doc available) (requirements : Sub [.tokens] available := by decide) :
    Doc (.lemma :: .pos :: available) :=
  morphology.lemmatizeDoc (tagger.tagDoc doc requirements)
    (morphologyRequirements requirements)

/-- Fused English analysis preserves every structural document invariant. -/
theorem tagAndLemmatizeDoc_wf (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) (doc : Doc available) (wellFormed : doc.WF)
    (requirements : Sub [.tokens] available := by decide) :
    (tagAndLemmatizeDoc tagger morphology doc requirements).WF :=
  morphology.lemmatizeDoc_wf (tagger.tagDoc doc requirements)
    (tagger.tagDoc_wf doc wellFormed requirements)
    (morphologyRequirements requirements)

/-- Fused English analysis preserves token and sentence semantics. -/
theorem tagAndLemmatizeDoc_semanticWF (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) (doc : Doc available) (semantic : doc.SemanticWF)
    (requirements : Sub [.tokens] available := by decide) :
    (tagAndLemmatizeDoc tagger morphology doc requirements).SemanticWF :=
  morphology.lemmatizeDoc_semanticWF (tagger.tagDoc doc requirements)
    (tagger.tagDoc_semanticWF doc semantic requirements)
    (morphologyRequirements requirements)

/-- Functional token-to-POS-to-lemma English annotator. -/
def tagAndLemmatizeAnnotator (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) : Ann Id [.tokens] [.lemma, .pos] :=
  Ann.fromPure "english" fun requirements doc ↦
    tagAndLemmatizeDoc tagger morphology doc requirements

/-- Tokenize and sentence-split raw text, then add its POS and lemma columns. -/
def analyzeText (tokenizer : Tokenize.Tokenizer) (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) (text : String)
    (sentenceConfig : Tokenize.Sentence.Config := {}) :
    Doc [.lemma, .pos, .sents, .tokens] :=
  tagAndLemmatizeDoc tagger morphology (tokenizer.process text sentenceConfig)

end Nlp.English

namespace Nlp.NLP

/-- Check an English pipeline input without changing its statically indexed shape. -/
private def validateEnglishInput (doc : Doc available) : NLP (Doc available) :=
  match doc.checkedSemantic with
  | .ok checked => pure checked
  | .error cause =>
      throw <| .invalidInput "English pipeline input"
        s!"semantic validation failed: {repr cause}"

/-- Run the pure fused kernel after its caller has established the checked boundary. -/
private def tagAndLemmatizeChecked (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) (doc : Doc available)
    (requirements : Sub [.tokens] available) :
    NLP (Doc (.lemma :: .pos :: available)) := do
  checkCancelled
  let output := English.tagAndLemmatizeDoc tagger morphology doc requirements
  checkCancelled
  return output

/-- Tag and lemmatize one document after exactly one semantic input validation. -/
def tagAndLemmatize (tagger : Sequence.PosTagger) (morphology : Morphology.Model)
    (doc : Doc available) (requirements : Sub [.tokens] available := by decide) :
    NLP (Doc (.lemma :: .pos :: available)) := do
  checkCancelled
  let checked ← validateEnglishInput doc
  tagAndLemmatizeChecked tagger morphology checked requirements

/-- Tag and lemmatize a corpus with token-weighted bounded concurrency and stable order. -/
@[inline] def tagAndLemmatizeMany (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Doc (.lemma :: .pos :: available))) :=
  traverseArrayWeighted documents Doc.size fun doc ↦
    tagAndLemmatize tagger morphology doc requirements

/-- Analyze a corpus with an explicit minimum token weight per scheduling unit. -/
@[inline] def tagAndLemmatizeManyWithMinTokens (minTokens : Nat)
    (tagger : Sequence.PosTagger) (morphology : Morphology.Model)
    (documents : Array (Doc available))
    (requirements : Sub [.tokens] available := by decide) :
    NLP (Array (Doc (.lemma :: .pos :: available))) :=
  traverseArrayWeightedWithMinWeight minTokens documents Doc.size fun doc ↦
    tagAndLemmatize tagger morphology doc requirements

/-- Tokenize, sentence-split, validate once, tag, and lemmatize one raw string. -/
def analyzeEnglishText (tokenizer : Tokenize.Tokenizer) (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) (text : String)
    (sentenceConfig : Tokenize.Sentence.Config := {}) :
    NLP (Doc [.lemma, .pos, .sents, .tokens]) := do
  checkCancelled
  let tokenized := tokenizer.process text sentenceConfig
  checkCancelled
  let checked ← validateEnglishInput tokenized
  tagAndLemmatizeChecked tagger morphology checked (by decide)

/-- Analyze raw strings with UTF-8-byte-weighted bounded concurrency and stable order. -/
@[inline] def analyzeEnglishTexts (tokenizer : Tokenize.Tokenizer)
    (tagger : Sequence.PosTagger) (morphology : Morphology.Model)
    (texts : Array String) (sentenceConfig : Tokenize.Sentence.Config := {}) :
    NLP (Array (Doc [.lemma, .pos, .sents, .tokens])) :=
  traverseArrayWeighted texts String.utf8ByteSize fun text ↦
    analyzeEnglishText tokenizer tagger morphology text sentenceConfig

/-- Analyze raw strings with an explicit minimum UTF-8 byte weight per scheduling unit. -/
@[inline] def analyzeEnglishTextsWithMinBytes (minBytes : Nat)
    (tokenizer : Tokenize.Tokenizer) (tagger : Sequence.PosTagger)
    (morphology : Morphology.Model) (texts : Array String)
    (sentenceConfig : Tokenize.Sentence.Config := {}) :
    NLP (Array (Doc [.lemma, .pos, .sents, .tokens])) :=
  traverseArrayWeightedWithMinWeight minBytes texts String.utf8ByteSize fun text ↦
    analyzeEnglishText tokenizer tagger morphology text sentenceConfig

end Nlp.NLP
