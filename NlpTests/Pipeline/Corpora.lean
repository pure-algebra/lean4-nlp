import Nlp.Pipeline.Corpora

namespace NlpTests.Pipeline.Corpora

open Nlp

private def withTempDir (action : System.FilePath → IO α) : IO α := do
  let directory ← IO.FS.createTempDir
  try
    action directory
  finally
    if ← directory.isDir then
      IO.FS.removeDirAll directory

private def compactSample : String :=
  "# sent_id = 1\n" ++
    "1\tcat\tcat\tNOUN\tNN\t_\t0\troot\t_\t_\n\n"

private def losslessSample : String :=
  "# sent_id = 1\n" ++
    "1\tcat\tcat\tNOUN\tNN\t_\t0\troot\t_\t_\n\n"

def testReadConlluRows : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "sample.conllu"
  IO.FS.writeFile path compactSample
  match ← NLP.runIO {} <| NLP.readConlluRows path with
  | .ok sentences =>
      match sentences.toList with
      | [sentence] =>
        match sentence.toList with
        | [row] =>
          if row.form != "cat" || row.head != some 0 then
            throw <| IO.userError "compact CoNLL-U reader changed the parsed row"
        | _ => throw <| IO.userError "compact CoNLL-U reader returned the wrong row count"
      | _ => throw <| IO.userError "compact CoNLL-U reader returned the wrong sentence count"
  | .error _ => throw <| IO.userError "compact CoNLL-U file read failed"

def testConlluRowsErrorLocation : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "malformed.conllu"
  IO.FS.writeFile path "1\ttoo-few\n"
  match ← NLP.runIO {} <| NLP.readConlluRows path with
  | .error (.invalidInput location why) =>
      if location != path.toString ||
          !why.startsWith "invalid CoNLL-U corpus: line 1:" then
        throw <| IO.userError "compact CoNLL-U failure lost its path or parser context"
  | _ => throw <| IO.userError "malformed compact CoNLL-U did not fail"

def testReadLosslessConllu : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "lossless.conllu"
  IO.FS.writeFile path losslessSample
  match ← NLP.runIO {} <| NLP.readConllu path with
  | .ok sentences =>
      match sentences.toList with
      | [sentence] =>
        if sentence.comments != #["# sent_id = 1"] || sentence.rows.size != 1 ||
            sentence.lineEnding != .lf then
          throw <| IO.userError "lossless CoNLL-U reader discarded source structure"
      | _ => throw <| IO.userError "lossless CoNLL-U reader returned the wrong sentence count"
  | .error _ => throw <| IO.userError "lossless CoNLL-U file read failed"

def testReadConlluDocs : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "document.conllu"
  IO.FS.writeFile path losslessSample
  match ← NLP.runIO {} <| NLP.readConlluDocs path with
  | .ok documents =>
      match documents.toList with
      | [document] =>
        if document.text != "cat" || document.forms != #["cat"] ||
            document.pos != #["NOUN"] || document.head != #[0] ||
            document.deprel != #["root"] then
          throw <| IO.userError "CoNLL-U document projection changed annotations"
      | _ => throw <| IO.userError "CoNLL-U projection returned the wrong document count"
  | .error _ => throw <| IO.userError "effectful CoNLL-U document projection failed"

def testProjectionErrorLocation : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "bad-head.conllu"
  IO.FS.writeFile path "1\tcat\tcat\tNOUN\tNN\t_\tx\troot\t_\t_\n\n"
  match ← NLP.runIO {} <| NLP.readConlluDocs path with
  | .error (.invalidInput location why) =>
      if location != path.toString ||
          !why.startsWith "invalid CoNLL-U sentence 1: Nlp.IO.ConlluError.malformedHead" then
        throw <| IO.userError "CoNLL-U projection failure lost its sentence and path"
  | _ => throw <| IO.userError "invalid CoNLL-U dependency projection did not fail"

def testLosslessSyntaxErrorLocation : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "truncated.conllu"
  IO.FS.writeFile path "1\tcat\tcat\tNOUN\tNN\t_\t0\troot\t_\t_"
  match ← NLP.runIO {} <| NLP.readConllu path with
  | .error (.invalidInput location why) =>
      if location != path.toString ||
          !why.startsWith "invalid lossless CoNLL-U corpus:" then
        throw <| IO.userError "lossless CoNLL-U failure lost its path or parser context"
  | _ => throw <| IO.userError "truncated lossless CoNLL-U did not fail"

def testReadPtbWithInterner : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "trees.mrg"
  IO.FS.writeFile path "(S (NN cat))\n(S (VB sleeps))\n"
  let .ok (seeded, seedId) := Interner.empty.intern "seed"
    | throw <| IO.userError "could not seed the PTB test interner"
  match ← NLP.runIO {} <| NLP.readPtbWith seeded path with
  | .ok (interner, trees) =>
      if interner.name? seedId != some "seed" || trees.size != 2 ||
          trees.foldl (fun width tree ↦ width + tree.width) 0 != 2 then
        throw <| IO.userError "effectful PTB reader did not preserve interning or trees"
  | .error _ => throw <| IO.userError "effectful PTB file read failed"

def testPtbErrorLocation : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "malformed.mrg"
  IO.FS.writeFile path "(S (NN cat)"
  match ← NLP.runIO {} <| NLP.readPtb path with
  | .error (.invalidInput location why) =>
      if location != path.toString || !why.startsWith "invalid PTB corpus:" then
        throw <| IO.userError "PTB failure lost its path or parser context"
  | _ => throw <| IO.userError "malformed PTB did not fail"

def testCancellation : IO Unit := withTempDir fun directory ↦ do
  let path := directory / "cancelled.conllu"
  IO.FS.writeFile path losslessSample
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  let result ← liftM <| (NLP.runIn env (NLP.readConlluDocs path)).toBaseIO
  match result with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "effectful corpus reader lost its cancellation reason"

#eval testReadConlluRows
#eval testConlluRowsErrorLocation
#eval testReadLosslessConllu
#eval testReadConlluDocs
#eval testProjectionErrorLocation
#eval testLosslessSyntaxErrorLocation
#eval testReadPtbWithInterner
#eval testPtbErrorLocation
#eval testCancellation

end NlpTests.Pipeline.Corpora
