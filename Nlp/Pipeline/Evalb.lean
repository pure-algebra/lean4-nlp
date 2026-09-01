import Nlp.Eval.Evalb
import Nlp.Pipeline.Files

/-!
# Effectful EVALB file facade

The EVALB implementation remains functional. This module owns filesystem access, cancellation,
path-aware error adaptation, and the upstream `MAX_ERROR` corpus policy. Per-sentence valid,
skipped, and error statuses remain data whenever the corpus stays within that limit.
-/

namespace Nlp.NLP.Evalb

open Nlp.Eval.Evalb

private def orInvalid (location context : String) (result : Except Error α) : NLP α :=
  match result with
  | .ok value => pure value
  | .error cause => throw <| .invalidInput location s!"{context}: {reprStr cause}"

/-- Read and parse an upstream EVALB `.prm` file without compiling its lookup tables. -/
def readParams (path : System.FilePath) : NLP Params := do
  let contents ← NLP.readFile path
  let params ← orInvalid path.toString "invalid EVALB parameter file" <| parseParams contents
  NLP.checkCancelled
  return params

/-- Read, validate, and compile an upstream EVALB `.prm` file for repeated scoring. -/
def loadParams (path : System.FilePath) : NLP CompiledParams := do
  let params ← readParams path
  let compiled ← orInvalid path.toString "invalid EVALB parameter configuration" <|
    params.compile
  NLP.checkCancelled
  return compiled

private def corpusLocation (goldPath testPath : System.FilePath) : String :=
  s!"gold={goldPath.toString}; test={testPath.toString}"

private def enforceErrorLimit (params : CompiledParams) (goldPath testPath : System.FilePath)
    (score : CorpusScore) : NLP CorpusScore := do
  if params.source.maxErrors < score.all.errors then
    let why := s!"EVALB MAX_ERROR exceeded: {score.all.errors} sentence errors > " ++
      s!"{params.source.maxErrors}"
    throw <| .invalidInput (corpusLocation goldPath testPath) why
  return score

/--
Read and score aligned PTB corpus files with already compiled parameters.

Pure EVALB failures are adapted to `Fail.invalidInput` at the path that supplied the invalid data.
Sentence-level scoring errors remain in `CorpusScore.results`. After the full deterministic score,
the action fails exactly when their total is greater than `params.source.maxErrors`; skipped
sentences do not count toward that threshold.
-/
def scoreFilesWith (params : CompiledParams) (goldPath testPath : System.FilePath) :
    NLP CorpusScore := do
  let goldText ← NLP.readFile goldPath
  let testText ← NLP.readFile testPath
  let (afterGold, goldCorpus) ←
    orInvalid goldPath.toString "invalid gold PTB corpus" <|
      parsePtbCorpus Interner.empty goldText
  NLP.checkCancelled
  let (interner, testCorpus) ←
    orInvalid testPath.toString "invalid test PTB corpus" <|
      parsePtbCorpus afterGold testText
  NLP.checkCancelled
  let score ← orInvalid (corpusLocation goldPath testPath)
    "could not score aligned EVALB corpora" <|
      scoreCorpusWith params interner goldCorpus testCorpus
  NLP.checkCancelled
  enforceErrorLimit params goldPath testPath score

/-- Load an EVALB parameter file, then read and score aligned gold and test PTB corpus files. -/
def scoreFiles (paramsPath goldPath testPath : System.FilePath) : NLP CorpusScore := do
  let params ← loadParams paramsPath
  scoreFilesWith params goldPath testPath

end Nlp.NLP.Evalb
