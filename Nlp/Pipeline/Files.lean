import Nlp.Pipeline.Runtime

/-!
# Filesystem effects

This module adapts `IO.Error` at the `NLP` boundary and provides a conservative atomic text install.
Lean's portable filesystem API does not promise atomic replacement of an existing destination, so
`writeFileAtomic` implements the safe create-new subset: it never overwrites a destination.
-/

namespace Nlp.NLP

/-- Lift ordinary `IO`, preserving its error as the typed fatal `Fail.io` case. -/
@[inline] def fromIO (action : IO α) : NLP α :=
  fun _ ↦ EIO.adapt Fail.io action

/-- Read one UTF-8 text file with cooperative checks on both sides of the blocking operation. -/
def readFile (path : System.FilePath) : NLP String := do
  checkCancelled
  let contents ← fromIO <| IO.FS.readFile path
  checkCancelled
  return contents

/--
Read one complete binary file with cooperative checks around the blocking operation.

This low-level operation has no byte cap. Model and untrusted-input loaders should use
`readBytesWithLimit` so the limit is enforced while the file is being read.
-/
def readBytes (path : System.FilePath) : NLP ByteArray := do
  checkCancelled
  let contents ← fromIO <| IO.FS.readBinFile path
  checkCancelled
  return contents

private inductive BoundedReadResult where
  | ok (bytes : ByteArray)
  | tooLarge (observed : Nat)
  | cancelled (reason : Std.CancellationReason)

private def readBytesWithLimitIO (cancellation : Std.CancellationContext)
    (path : System.FilePath) (maxBytes : Nat) : IO BoundedReadResult := do
  let metadata ← path.metadata
  let advertised := metadata.byteSize.toNat
  if maxBytes < advertised then
    return .tooLarge advertised
  IO.FS.withFile path .read fun handle ↦ do
    let mut bytes := ByteArray.emptyWithCapacity (min advertised maxBytes)
    while true do
      if let some reason := ← cancellation.getCancellationReason then
        return .cancelled reason
      if ← IO.checkCanceled then
        return .cancelled .cancel
      let remaining := maxBytes - bytes.size
      let request := min 65_536 (remaining + 1)
      let chunk ← handle.read (USize.ofNat request)
      if chunk.isEmpty then
        break
      if remaining < chunk.size then
        return .tooLarge (bytes.size + chunk.size)
      bytes := bytes ++ chunk
    return .ok bytes

/--
Read at most `maxBytes`, rejecting oversized files before or during allocation.

The metadata check is only an early rejection. Reads remain capped at `maxBytes + 1`, so a file
that grows after metadata lookup cannot bypass the limit. Cancellation is checked between chunks.
-/
def readBytesWithLimit (path : System.FilePath) (maxBytes : Nat) : NLP ByteArray := do
  checkCancelled
  let cancellation := (← read).cancellation
  match ← fromIO <| readBytesWithLimitIO cancellation path maxBytes with
  | .ok bytes =>
      checkCancelled
      return bytes
  | .tooLarge observed =>
      throw <| .invalidInput path.toString
        s!"binary file has at least {observed} bytes; configured limit is {maxBytes}"
  | .cancelled reason => throw <| .cancelled reason

/-- Deterministic paths used by the create-new atomic writer. -/
structure AtomicWritePaths where
  directory : System.FilePath
  payload : System.FilePath
  deriving Repr, DecidableEq

/--
Pure, deterministic temp-path planning. The private directory is an atomic exclusivity claim; its
payload stays on the destination filesystem even though Lean lacks create-temp-in-directory.
-/
def atomicWritePaths (target : System.FilePath) (processId : UInt32) (nonce : Nat) :
    Except Fail AtomicWritePaths := do
  let some fileName := target.fileName
    | throw <| .invalidInput target.toString "atomic-write target has no file name"
  let tempName := s!".{fileName}.nlp-tmp-{processId}-{nonce}"
  let directory := target.withFileName tempName
  return { directory, payload := directory / "payload" }

private def ignoreCleanupError (action : IO Unit) : IO Unit := do
  try action catch _ => pure ()

/-- Best-effort cleanup must never change the result after the destination becomes visible. -/
private def cleanupAtomicWrite (paths : AtomicWritePaths) : IO Unit := do
  ignoreCleanupError do
    if ← paths.payload.pathExists then
      IO.FS.removeFile paths.payload
  ignoreCleanupError do
    if ← paths.directory.isDir then
      IO.FS.removeDir paths.directory

private def installNewText (paths : AtomicWritePaths) (target : System.FilePath)
    (contents : String) : IO Unit := do
  IO.FS.createDir paths.directory
  try
    IO.FS.withFile paths.payload .write fun handle ↦ do
      handle.putStr contents
      handle.flush
    IO.FS.hardLink paths.payload target
  finally
    cleanupAtomicWrite paths

namespace AtomicWrite

/--
Run one install operation at its linearization boundary.

Cancellation is checked before entry. Once `install` returns successfully, this returns success
without a trailing check: reporting cancellation after a successful commit would contradict the
visible filesystem state.
-/
def commit (install : IO α) : NLP α := do
  checkCancelled
  fromIO install

end AtomicWrite

/--
Install a new UTF-8 file atomically using deterministic temp naming.

The directory claim fails safely on a nonce collision. The final hard-link operation fails if the
destination exists, so this function never replaces or truncates existing data. A successful return
means the destination has complete contents. Cleanup is best-effort: a successful visible commit is
never reported as a failure merely because the private temporary directory could not be removed.
-/
def writeFileAtomicWithNonce (target : System.FilePath) (contents : String)
    (processId : UInt32) (nonce : Nat) : NLP Unit := do
  let paths ← EIO.ofExcept <| atomicWritePaths target processId nonce
  AtomicWrite.commit <| installNewText paths target contents

/--
Install a new UTF-8 file atomically with a process/time-derived temp name.

This is atomic visibility, not a crash-durability guarantee: Lean exposes buffer flush but no
portable file or directory `fsync`. Existing destinations are deliberately rejected.
-/
def writeFileAtomic (target : System.FilePath) (contents : String) : NLP Unit := do
  let processId ← liftM <| IO.Process.getPID
  let nonce ← liftM <| IO.monoNanosNow
  writeFileAtomicWithNonce target contents processId nonce

end Nlp.NLP
