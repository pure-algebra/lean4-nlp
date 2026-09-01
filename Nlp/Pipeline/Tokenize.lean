import Nlp.Pipeline.Annotate
import Nlp.Pipeline.Laws
import Nlp.Tokenize

/-!
# Tokenization pipeline boundary

Tokenization is an exact-index transform, not a polymorphic layer-extending `Ann`: rebuilding token
boundaries must discard any stale POS, lemma, NER, dependency, or parse columns. The pure API keeps
the scanner and sentence splitter directly available; the `NLP` facade adds semantic validation,
cooperative cancellation, stable corpus order, and UTF-8-byte-weighted scheduling.
-/

namespace Nlp.Tokenize

namespace Tokenization

/-- Project source-indexed tokens into the document struct-of-arrays representation. -/
def toDoc (tokenization : Tokenization) : Doc [.tokens] := Id.run do
  let mut spans := Array.emptyWithCapacity tokenization.tokens.size
  let mut forms := Array.emptyWithCapacity tokenization.tokens.size
  for token in tokenization.tokens do
    spans := spans.push token.span
    forms := forms.push token.original
  return { text := tokenization.text, spans, forms }

/-- Project and validate a token document at a public or model boundary. -/
def checkedDoc (tokenization : Tokenization) : Except Doc.SemanticError (Doc [.tokens]) :=
  tokenization.toDoc.checkedSemantic

end Tokenization

namespace Sentence.Segmentation

/-- Project sentence ends and their source tokens into an annotated document. -/
def toDoc (segmentation : Sentence.Segmentation) : Doc [.sents, .tokens] :=
  { segmentation.source.toDoc with sentEnd := segmentation.ends }

/-- Project and validate a sentence-segmented document at a public or model boundary. -/
def checkedDoc (segmentation : Sentence.Segmentation) :
    Except Doc.SemanticError (Doc [.sents, .tokens]) :=
  segmentation.toDoc.checkedSemantic

end Sentence.Segmentation

namespace Tokenizer

/-- Tokenize raw text directly into the token document layer. -/
@[inline] def tokenizeDoc (tokenizer : Tokenizer) (text : String) : Doc [.tokens] :=
  (tokenizer.tokenize text).toDoc

/-- Tokenize and validate the document projection. -/
@[inline] def tokenizeDocChecked (tokenizer : Tokenizer) (text : String) :
    Except Doc.SemanticError (Doc [.tokens]) :=
  (tokenizer.tokenize text).checkedDoc

/-- Tokenize and sentence-split raw text with source-indexed, allocation-aware kernels. -/
@[inline] def process (tokenizer : Tokenizer) (text : String)
    (sentenceConfig : Sentence.Config := {}) : Doc [.sents, .tokens] :=
  (Sentence.split (tokenizer.tokenize text) sentenceConfig).toDoc

/-- Exact pure tokenizer arrow; hidden fields in the input document are deliberately discarded. -/
def annotator (tokenizer : Tokenizer) : Arr Id [] [.tokens] :=
  fun doc ↦ tokenizer.tokenizeDoc doc.text

/-- Exact pure tokenize-plus-sentence-split arrow matching the usual application entry point. -/
def pipeline (tokenizer : Tokenizer) (sentenceConfig : Sentence.Config := {}) :
    Arr Id [] [.sents, .tokens] :=
  fun doc ↦ tokenizer.process doc.text sentenceConfig

end Tokenizer

end Nlp.Tokenize

namespace Nlp.NLP

private def validateTokenDoc (document : Doc [.tokens]) : NLP (Doc [.tokens]) :=
  match document.checkedSemantic with
  | .ok checked => pure checked
  | .error cause =>
      throw <| .invalidInput "tokenizer output" s!"semantic validation failed: {repr cause}"

private def validateSentenceDoc (document : Doc [.sents, .tokens]) :
    NLP (Doc [.sents, .tokens]) :=
  match document.checkedSemantic with
  | .ok checked => pure checked
  | .error cause =>
      throw <| .invalidInput "sentence splitter output"
        s!"semantic validation failed: {repr cause}"

/-- Tokenize one string through the checked effectful application boundary. -/
def tokenizeText (tokenizer : Tokenize.Tokenizer) (text : String) :
    NLP (Doc [.tokens]) := do
  checkCancelled
  let document := tokenizer.tokenizeDoc text
  checkCancelled
  let checked ← validateTokenDoc document
  checkCancelled
  return checked

/-- Tokenize and sentence-split one string through the checked effectful boundary. -/
def processText (tokenizer : Tokenize.Tokenizer) (text : String)
    (sentenceConfig : Tokenize.Sentence.Config := {}) : NLP (Doc [.sents, .tokens]) := do
  checkCancelled
  let document := tokenizer.process text sentenceConfig
  checkCancelled
  let checked ← validateSentenceDoc document
  checkCancelled
  return checked

/-- Tokenize a corpus with stable order and byte-weighted bounded scheduling. -/
@[inline] def tokenizeTexts (tokenizer : Tokenize.Tokenizer) (texts : Array String) :
    NLP (Array (Doc [.tokens])) :=
  traverseArrayWeighted texts String.utf8ByteSize (tokenizeText tokenizer)

/-- Tokenize a corpus using an explicit minimum UTF-8 byte weight per scheduling unit. -/
@[inline] def tokenizeTextsWithMinBytes (minBytes : Nat) (tokenizer : Tokenize.Tokenizer)
    (texts : Array String) : NLP (Array (Doc [.tokens])) :=
  traverseArrayWeightedWithMinWeight minBytes texts String.utf8ByteSize (tokenizeText tokenizer)

/-- Tokenize and sentence-split a corpus with byte-weighted bounded scheduling. -/
@[inline] def processTexts (tokenizer : Tokenize.Tokenizer) (texts : Array String)
    (sentenceConfig : Tokenize.Sentence.Config := {}) :
    NLP (Array (Doc [.sents, .tokens])) :=
  traverseArrayWeighted texts String.utf8ByteSize fun text ↦
    processText tokenizer text sentenceConfig

/-- Process a corpus using an explicit minimum UTF-8 byte weight per scheduling unit. -/
@[inline] def processTextsWithMinBytes (minBytes : Nat) (tokenizer : Tokenize.Tokenizer)
    (texts : Array String) (sentenceConfig : Tokenize.Sentence.Config := {}) :
    NLP (Array (Doc [.sents, .tokens])) :=
  traverseArrayWeightedWithMinWeight minBytes texts String.utf8ByteSize
    fun text ↦ processText tokenizer text sentenceConfig

end Nlp.NLP
