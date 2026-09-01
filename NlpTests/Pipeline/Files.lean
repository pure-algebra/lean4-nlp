import Nlp.Pipeline.Files

namespace NlpTests.Pipeline.Files

open Nlp

def withTempDir (action : System.FilePath → IO α) : IO α := do
  let directory ← IO.FS.createTempDir
  try
    action directory
  finally
    if ← directory.isDir then
      IO.FS.removeDirAll directory

def testAtomicWriteRead : IO Unit := withTempDir fun directory ↦ do
  let target := directory / "result.txt"
  let action : NLP String := do
    NLP.writeFileAtomic target "alpha\nbeta\n"
    NLP.readFile target
  match ← NLP.runIO {} action with
  | .ok "alpha\nbeta\n" =>
      let entries ← directory.readDir
      if entries.size != 1 then
        throw <| IO.userError "atomic write leaked temporary artifacts"
  | _ => throw <| IO.userError "atomic write/read round trip failed"

private def testBinaryRead : IO Unit := withTempDir fun directory ↦ do
  let target := directory / "model.bin"
  let payload := ByteArray.mk #[0, 255, 1, 128]
  IO.FS.writeBinFile target payload
  match ← NLP.runIO {} (NLP.readBytes target) with
  | .ok found =>
      if found != payload then
        throw <| IO.userError "binary read changed payload bytes"
  | .error _ => throw <| IO.userError "binary read failed"

  match ← NLP.runIO {} (NLP.readBytesWithLimit target payload.size) with
  | .ok found =>
      if found != payload then
        throw <| IO.userError "bounded binary read changed payload bytes"
  | .error _ => throw <| IO.userError "exact bounded binary read failed"

  match ← NLP.runIO {} (NLP.readBytesWithLimit target (payload.size - 1)) with
  | .error (.invalidInput location why) =>
      unless location == target.toString && why.contains "configured limit is 3" do
        throw <| IO.userError "bounded binary read lost its limit diagnostic"
  | _ => throw <| IO.userError "one-short binary limit was accepted"

  let emptyTarget := directory / "empty.bin"
  IO.FS.writeBinFile emptyTarget {}
  match ← NLP.runIO {} (NLP.readBytesWithLimit emptyTarget 0) with
  | .ok found =>
      unless found.isEmpty do
        throw <| IO.userError "zero-limit empty binary read returned bytes"
  | .error _ => throw <| IO.userError "zero-limit empty binary read failed"

def testExistingTargetPreserved : IO Unit := withTempDir fun directory ↦ do
  let target := directory / "existing.txt"
  IO.FS.writeFile target "old"
  let paths := NLP.atomicWritePaths target 13 17
  let result ← NLP.runIO {} <|
    NLP.writeFileAtomicWithNonce target "new" 13 17
  let contents ← IO.FS.readFile target
  let tempWasRemoved ← (match paths with
    | .ok paths => do
        let present ← paths.directory.pathExists
        pure !present
    | .error _ => pure false : BaseIO Bool)
  match result with
  | .error (.io _) =>
      if contents != "old" || !tempWasRemoved then
        throw <| IO.userError "failed atomic install changed data or leaked temp files"
  | _ => throw <| IO.userError "atomic install replaced an existing destination"

def testFromIOError : IO Unit := do
  let action : NLP Unit := NLP.fromIO <| throw <| IO.userError "expected"
  match ← NLP.runIO {} action with
  | .error (.io _) => pure ()
  | _ => throw <| IO.userError "IO error was not preserved as Fail.io"

def testCancelledBeforeWrite : IO Unit := withTempDir fun directory ↦ do
  let target := directory / "cancelled.txt"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  let result ← liftM <|
    (NLP.runIn env (NLP.writeFileAtomicWithNonce target "data" 19 23)).toBaseIO
  match result with
  | .error (.cancelled .shutdown) =>
      if ← target.pathExists then
        throw <| IO.userError "pre-cancelled atomic write created a destination"
  | _ => throw <| IO.userError "pre-cancelled atomic write lost its reason"

def testCommitLinearization : IO Unit := withTempDir fun directory ↦ do
  let marker := directory / "committed.txt"
  let cancellation ← liftM <| Std.CancellationContext.new
  let env : Env := { config := {}, cancellation }
  let install : IO Unit := do
    IO.FS.writeFile marker "committed"
    cancellation.cancel .shutdown
  let result ← liftM <| (NLP.runIn env (NLP.AtomicWrite.commit install)).toBaseIO
  match result with
  | .ok () =>
      if !(← marker.pathExists) then
        throw <| IO.userError "successful commit did not reach its linearization point"
  | _ => throw <| IO.userError "successful commit was misreported as cancellation"

#eval testAtomicWriteRead
#eval testBinaryRead
#eval testExistingTargetPreserved
#eval testFromIOError
#eval testCancelledBeforeWrite
#eval testCommitLinearization

end NlpTests.Pipeline.Files
