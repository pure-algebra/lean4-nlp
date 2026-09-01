import Nlp.Pipeline.Evalb

namespace NlpTests.Pipeline.Evalb

open Nlp Nlp.Eval.Evalb

private def withTempDir (action : System.FilePath → IO α) : IO α := do
  let directory ← IO.FS.createTempDir
  try
    action directory
  finally
    if ← directory.isDir then
      IO.FS.removeDirAll directory

private def writeFixture (directory : System.FilePath) (params gold test : String) :
    IO (System.FilePath × System.FilePath × System.FilePath) := do
  let paramsPath := directory / "evalb.prm"
  let goldPath := directory / "gold.mrg"
  let testPath := directory / "test.mrg"
  IO.FS.writeFile paramsPath params
  IO.FS.writeFile goldPath gold
  IO.FS.writeFile testPath test
  return (paramsPath, goldPath, testPath)

def testScoreFiles : IO Unit := withTempDir fun directory ↦ do
  let (paramsPath, goldPath, testPath) ← writeFixture directory
    "LABELED 1\nCUTOFF_LEN 40\nMAX_ERROR 1\n"
    "(S (NN cat))\n"
    "(S (NN cat))\n"
  match ← NLP.runIO {} <| NLP.Evalb.scoreFiles paramsPath goldPath testPath with
  | .ok score =>
      match score.results[0]? with
      | some (SentenceResult.valid sentence) =>
          if sentence.words != 1 || score.all.valid != 1 then
            throw <| IO.userError "effectful EVALB score had unexpected counts"
      | _ => throw <| IO.userError "effectful EVALB did not preserve valid status"
  | .error _ => throw <| IO.userError "effectful EVALB file score failed"

def testSentenceErrorsRemainData : IO Unit := withTempDir fun directory ↦ do
  let (_, goldPath, testPath) ← writeFixture directory
    "MAX_ERROR 1\n"
    "(S (NN cat))\n"
    "(S (NN dog))\n"
  let .ok params := ({ Params.empty with maxErrors := 1 } : Params).compile
    | throw <| IO.userError "test parameters did not compile"
  match ← NLP.runIO {} <| NLP.Evalb.scoreFilesWith params goldPath testPath with
  | .ok score =>
      match score.results[0]? with
      | some (SentenceResult.error 1 1 (.wordMismatch 0 "cat" "dog")) =>
          if score.all.errors != 1 then
            throw <| IO.userError "sentence error was not included in the summary"
      | _ => throw <| IO.userError "sentence error was not preserved as data"
  | .error _ => throw <| IO.userError "MAX_ERROR boundary rejected an allowed error"

def testMaxErrorsExceeded : IO Unit := withTempDir fun directory ↦ do
  let (_, goldPath, testPath) ← writeFixture directory
    "MAX_ERROR 0\n"
    "(S (NN cat))\n"
    "(S (NN dog))\n"
  let .ok params := ({ Params.empty with maxErrors := 0 } : Params).compile
    | throw <| IO.userError "test parameters did not compile"
  match ← NLP.runIO {} <| NLP.Evalb.scoreFilesWith params goldPath testPath with
  | .error (.invalidInput location why) =>
      let expected := s!"gold={goldPath.toString}; test={testPath.toString}"
      if location != expected || !why.startsWith "EVALB MAX_ERROR exceeded:" then
        throw <| IO.userError "MAX_ERROR failure lost its corpus context"
  | _ => throw <| IO.userError "MAX_ERROR boundary did not fail"

def testParameterErrorMapping : IO Unit := withTempDir fun directory ↦ do
  let paramsPath := directory / "invalid.prm"
  let goldPath := directory / "missing-gold.mrg"
  let testPath := directory / "missing-test.mrg"
  IO.FS.writeFile paramsPath "CUTOFF_LEN nope\n"
  match ← NLP.runIO {} <| NLP.Evalb.scoreFiles paramsPath goldPath testPath with
  | .error (.invalidInput location why) =>
      if location != paramsPath.toString ||
          !why.startsWith "invalid EVALB parameter file:" then
        throw <| IO.userError "parameter error lost its path or parsing context"
  | _ => throw <| IO.userError "parameter error was not mapped to Fail.invalidInput"

def testGoldErrorMapping : IO Unit := withTempDir fun directory ↦ do
  let (_, goldPath, testPath) ← writeFixture directory
    "MAX_ERROR 1\n"
    "((S (NN cat)))\n"
    "(S (NN cat))\n"
  let .ok params := Params.empty.compile
    | throw <| IO.userError "test parameters did not compile"
  match ← NLP.runIO {} <| NLP.Evalb.scoreFilesWith params goldPath testPath with
  | .error (.invalidInput location why) =>
      if location != goldPath.toString || !why.startsWith "invalid gold PTB corpus:" then
        throw <| IO.userError "gold parse error lost its path or corpus context"
  | _ => throw <| IO.userError "gold parse error was not mapped to Fail.invalidInput"

def testCancellationMapping : IO Unit := withTempDir fun directory ↦ do
  let (paramsPath, goldPath, testPath) ← writeFixture directory
    "MAX_ERROR 1\n"
    "(S (NN cat))\n"
    "(S (NN cat))\n"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  let result ← liftM <|
    (NLP.runIn env (NLP.Evalb.scoreFiles paramsPath goldPath testPath)).toBaseIO
  match result with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "effectful EVALB lost its cancellation reason"

#eval testScoreFiles
#eval testSentenceErrorsRemainData
#eval testMaxErrorsExceeded
#eval testParameterErrorMapping
#eval testGoldErrorMapping
#eval testCancellationMapping

end NlpTests.Pipeline.Evalb
