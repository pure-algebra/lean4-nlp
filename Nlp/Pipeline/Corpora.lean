import Nlp.IO.CoNLLU
import Nlp.IO.ConlluReader
import Nlp.IO.Ptb
import Nlp.Pipeline.Files

/-!
# Effectful corpus readers

The parsers in `Nlp.IO` remain total, deterministic functions over text. This module is the
user-facing effect boundary: it reads files, preserves typed cancellation and I/O failures, and
adds source locations to malformed-input failures.
-/

namespace Nlp.NLP

private def orInvalidString (location context : String) (result : Except String α) : NLP α :=
  match result with
  | .ok value => pure value
  | .error cause => throw <| .invalidInput location s!"{context}: {cause}"

private def orInvalid [Repr ε] (location context : String) (result : Except ε α) : NLP α :=
  match result with
  | .ok value => pure value
  | .error cause => throw <| .invalidInput location s!"{context}: {reprStr cause}"

/--
Parse the compact CoNLL-U representation that discards comments but preserves all row shapes.

`location` is an opaque caller-supplied source name used only in `Fail.invalidInput` diagnostics.
The pure equivalent is `Nlp.IO.parseSentences`.
-/
def parseConlluRows (location contents : String) : NLP (Array (Array IO.CoNLLURow)) := do
  checkCancelled
  let sentences ← orInvalidString location "invalid CoNLL-U corpus" <|
    IO.parseSentences contents
  checkCancelled
  return sentences

/-- Read and parse the compact, comment-discarding CoNLL-U representation. -/
def readConlluRows (path : System.FilePath) : NLP (Array (Array IO.CoNLLURow)) := do
  let contents ← readFile path
  parseConlluRows path.toString contents

/--
Parse canonical CoNLL-U losslessly, retaining comments, row spelling, and line endings.

The pure equivalent is `Nlp.IO.parseConllu`.
-/
def parseConllu (location contents : String) : NLP (Array IO.ConlluSentence) := do
  checkCancelled
  let sentences ← orInvalid location "invalid lossless CoNLL-U corpus" <|
    IO.parseConllu contents
  checkCancelled
  return sentences

/-- Read and parse canonical CoNLL-U without discarding source structure. -/
def readConllu (path : System.FilePath) : NLP (Array IO.ConlluSentence) := do
  let contents ← readFile path
  parseConllu path.toString contents

/--
Project lossless CoNLL-U sentences into checked dependency documents.

Cancellation is checked between sentences. A projection failure retains the corpus location and
reports the one-based sentence number in its explanation.
-/
def projectConlluDocs (location : String) (sentences : Array IO.ConlluSentence) :
    NLP (Array (Doc [.dep, .lemma, .pos, .sents, .tokens])) := do
  let mut documents := #[]
  let mut sentenceNumber := 0
  for sentence in sentences do
    checkCancelled
    sentenceNumber := sentenceNumber + 1
    let document ← orInvalid location s!"invalid CoNLL-U sentence {sentenceNumber}" <|
      sentence.toDoc
    documents := documents.push document
  checkCancelled
  return documents

/-- Parse lossless CoNLL-U text and project every sentence into a checked dependency document. -/
def parseConlluDocs (location contents : String) :
    NLP (Array (Doc [.dep, .lemma, .pos, .sents, .tokens])) := do
  let sentences ← parseConllu location contents
  projectConlluDocs location sentences

/-- Read lossless CoNLL-U and project every sentence into a checked dependency document. -/
def readConlluDocs (path : System.FilePath) :
    NLP (Array (Doc [.dep, .lemma, .pos, .sents, .tokens])) := do
  let contents ← readFile path
  parseConlluDocs path.toString contents

/--
Parse PTB trees while persistently extending an existing interner.

The pure equivalent is `Nlp.IO.parseBracketed`.
-/
def parsePtbWith (interner : Interner) (location contents : String) :
    NLP (Interner × Array Tree) := do
  checkCancelled
  let parsed ← orInvalid location "invalid PTB corpus" <|
    IO.parseBracketed interner contents
  checkCancelled
  return parsed

/-- Parse PTB trees into a fresh interner. -/
def parsePtb (location contents : String) : NLP (Interner × Array Tree) :=
  parsePtbWith Interner.empty location contents

/-- Read PTB trees while persistently extending an existing interner. -/
def readPtbWith (interner : Interner) (path : System.FilePath) :
    NLP (Interner × Array Tree) := do
  let contents ← readFile path
  parsePtbWith interner path.toString contents

/-- Read PTB trees into a fresh interner. -/
def readPtb (path : System.FilePath) : NLP (Interner × Array Tree) :=
  readPtbWith Interner.empty path

end Nlp.NLP
