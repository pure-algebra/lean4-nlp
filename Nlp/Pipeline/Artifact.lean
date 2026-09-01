import Nlp.Model.Artifact
import Nlp.Pipeline.Files

/-!
# Effectful native artifact loading

This module owns the filesystem boundary for native model artifacts. It opens one handle, reads and
preflights the fixed header before allocating the declared payload, reads exactly that payload plus
one trailing-byte probe, and checks cancellation between bounded I/O and checksum chunks.
-/

namespace Nlp.NLP

namespace Artifact

open Nlp.Model.Artifact

private inductive ReadResult where
  | ok (prepared : PreparedHeader) (bytes : ByteArray)
  | missing
  | corrupt (cause : Error)
  | cancelled (reason : Std.CancellationReason)

private def cancellationReason? (cancellation : Std.CancellationContext) :
    IO (Option Std.CancellationReason) := do
  if let some reason := ← cancellation.getCancellationReason then
    return some reason
  if ← IO.checkCanceled then
    return some .cancel
  return none

private def readOneHandle (cancellation : Std.CancellationContext)
    (config : Nlp.Model.Artifact.Config) (path : System.FilePath) : IO ReadResult := do
  try
    IO.FS.withFile path .read fun handle ↦ do
      let mut header := ByteArray.emptyWithCapacity Layout.headerSize
      while header.size < Layout.headerSize do
        if let some reason := ← cancellationReason? cancellation then
          return .cancelled reason
        let remaining := Layout.headerSize - header.size
        let chunk ← handle.read (USize.ofNat remaining)
        if chunk.isEmpty then
          break
        header := header ++ chunk
      if header.size < Layout.headerSize then
        return .corrupt <| .truncated 0 Layout.headerSize header.size
      match prepareHeaderWith config header with
      | .error cause => return .corrupt cause
      | .ok prepared =>
          let mut bytes := ByteArray.emptyWithCapacity prepared.totalBytes
          bytes := bytes ++ header
          while bytes.size < prepared.totalBytes do
            if let some reason := ← cancellationReason? cancellation then
              return .cancelled reason
            let remaining := prepared.totalBytes - bytes.size
            let request := min checksumChunkBytes remaining
            let chunk ← handle.read (USize.ofNat request)
            if chunk.isEmpty then
              break
            bytes := bytes ++ chunk
          if bytes.size < prepared.totalBytes then
            return .corrupt <| .truncated Layout.payloadOffset prepared.payloadBytes
              (bytes.size - Layout.payloadOffset)
          if let some reason := ← cancellationReason? cancellation then
            return .cancelled reason
          let trailing ← handle.read 1
          if !trailing.isEmpty then
            return .corrupt <| .trailingBytes prepared.totalBytes trailing.size
          return .ok prepared bytes
  catch cause =>
    match cause with
    | .noFileOrDirectory _ _ _ => return .missing
    | _ => throw cause

end Artifact

open Nlp.Model

/-- Stable user-facing detail for a rejected native artifact envelope. -/
def artifactErrorDetail : Artifact.Error → String
  | .totalBytesBudget found limit =>
      s!"envelope requires {found} bytes; configured total-byte limit is {limit}"
  | .truncated offset required found =>
      s!"truncated field or payload at byte {offset}: required {required} bytes, found {found}"
  | .invalidHeaderSize required found =>
      s!"fixed header requires exactly {required} bytes, found {found}"
  | .badMagic offset expected found =>
      s!"bad magic byte at {offset}: expected {expected}, found {found}"
  | .unsupportedVersion offset found =>
      s!"unsupported schema version {found} at byte {offset}"
  | .unsupportedKind offset found =>
      s!"unsupported payload kind {found} at byte {offset}"
  | .payloadLengthOverflow offset declared =>
      s!"payload length {declared} at byte {offset} overflows the envelope extent"
  | .payloadLengthUnrepresentable offset required =>
      s!"payload length {required} cannot be represented at byte {offset}"
  | .payloadBytesBudget offset required limit =>
      s!"payload at byte {offset} requires {required} bytes; configured limit is {limit}"
  | .trailingBytes offset count =>
      s!"found at least {count} trailing byte(s) after the declared extent at byte {offset}"
  | .checksumMismatch offset stored computed =>
      s!"checksum mismatch at byte {offset}: stored {stored}, computed {computed}"
  | .preparedHeaderMismatch offset expected found =>
      s!"header changed at byte {offset}: expected {expected}, found {found}"
  | .expectedKindMismatch offset expected found =>
      s!"payload kind mismatch at byte {offset}: expected {reprStr expected}, " ++
        s!"found {reprStr found}"
  | .expectedFeatureFingerprintMismatch offset expected found =>
      s!"feature fingerprint mismatch at byte {offset}: expected {expected.bits}, " ++
        s!"found {found.bits}"
  | .expectedTokenizerFingerprintMismatch offset expected found =>
      s!"tokenizer fingerprint mismatch at byte {offset}: expected {expected.bits}, " ++
        s!"found {found.bits}"

/--
Load, validate, and metadata-check one native artifact under explicit resource limits.

The file is opened exactly once. Header preflight happens before payload allocation, and the loader
never reads beyond the declared extent except for a one-byte trailing-data probe.
-/
def loadArtifactWith (config : Artifact.Config) (expected : Artifact.Metadata)
    (path : System.FilePath) : NLP Artifact.Checked := do
  checkCancelled
  let cancellation := (← read).cancellation
  match ← fromIO <| Artifact.readOneHandle cancellation config path with
  | .missing => throw <| .modelMissing path.toString
  | .corrupt cause => throw <| .modelCorrupt path.toString (artifactErrorDetail cause)
  | .cancelled reason => throw <| .cancelled reason
  | .ok prepared bytes =>
      match ← (Artifact.finishPreparedExpectedWithPoll prepared expected bytes
        checkCancelled).run with
      | .ok checked => return checked
      | .error cause => throw <| .modelCorrupt path.toString (artifactErrorDetail cause)

/-- Load and metadata-check one native artifact under production resource limits. -/
@[inline] def loadArtifact (expected : Artifact.Metadata)
    (path : System.FilePath) : NLP Artifact.Checked :=
  loadArtifactWith .default expected path

end Nlp.NLP
