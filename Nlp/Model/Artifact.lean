import Std.Data.ByteSlice

/-!
# Native model-artifact envelope

This module defines a deterministic binary envelope for model payloads. The fixed 44-byte header
contains an eight-byte magic value, a little-endian schema version and payload kind, two
little-endian fingerprints, the exact little-endian payload length, and a little-endian checksum.

The checksum is 64-bit FNV-1a over the header bytes before the checksum followed by the payload.
It is deterministic and useful only for accidental-corruption detection. It is not a
cryptographic hash, authenticity check, or signature.

Decoding checks total and payload budgets, all header fields, the exact total length, and the
checksum before retaining a zero-copy payload slice in the checked result.
-/

namespace Nlp.Model.Artifact

/-- Stable typed identifier for the uninterpreted payload carried by an artifact. -/
inductive PayloadKind where
  /-- A feature-rich linear-chain CRF named-entity model payload. -/
  | crfNer
  deriving Repr, DecidableEq, BEq, Inhabited

namespace PayloadKind

/-- Stable little-endian wire code for a payload kind. -/
@[inline] def code : PayloadKind → UInt16
  | .crfNer => 1

/-- Decode a stable wire code, rejecting codes not assigned by this schema. -/
@[inline] def ofCode? : UInt16 → Option PayloadKind
  | 1 => some .crfNer
  | _ => none

end PayloadKind

/-- Fingerprint selecting the exact feature-extraction schema expected by a payload. -/
structure FeatureFingerprint where
  /-- Exact caller-defined fingerprint bits. -/
  bits : UInt64
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Fingerprint selecting the exact tokenization profile expected by a payload. -/
structure TokenizerFingerprint where
  /-- Exact caller-defined fingerprint bits. -/
  bits : UInt64
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Typed metadata stored in every artifact header. -/
structure Metadata where
  /-- The uninterpreted payload's declared family. -/
  kind : PayloadKind
  /-- Exact feature-schema fingerprint. -/
  featureFingerprint : FeatureFingerprint
  /-- Exact tokenizer-profile fingerprint. -/
  tokenizerFingerprint : TokenizerFingerprint
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Resource limits applied before envelope allocation or decoded-payload exposure. -/
structure Config where
  /-- Maximum complete envelope size accepted from a caller. -/
  maxTotalBytes : Nat := 268_435_500
  /-- Maximum declared payload size accepted from a header. -/
  maxPayloadBytes : Nat := 268_435_456
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Config

/-- Production limits: a 256 MiB payload plus its fixed header. -/
def default : Config := {}

end Config

/-- Fixed eight-byte ASCII magic `L4NLPART`. -/
def magic : ByteArray :=
  [0x4c, 0x34, 0x4e, 0x4c, 0x50, 0x41, 0x52, 0x54].toByteArray

/-- The only schema version accepted by this decoder. -/
def schemaVersion : UInt16 := 1

namespace Layout

/-- Byte offset of the schema-version field. -/
def versionOffset : Nat := 8

/-- Byte offset of the payload-kind field. -/
def kindOffset : Nat := 10

/-- Byte offset of the feature-schema fingerprint. -/
def featureFingerprintOffset : Nat := 12

/-- Byte offset of the tokenizer-profile fingerprint. -/
def tokenizerFingerprintOffset : Nat := 20

/-- Byte offset of the declared payload length. -/
def payloadLengthOffset : Nat := 28

/-- Byte offset of the corruption-detection checksum. -/
def checksumOffset : Nat := 36

/-- Byte offset at which the uninterpreted payload begins. -/
def payloadOffset : Nat := 44

/-- Exact size of every artifact header. -/
def headerSize : Nat := payloadOffset

end Layout

/-- Typed reason that an artifact envelope could not be encoded, prepared, or decoded. -/
inductive Error where
  /-- The caller supplied more complete envelope bytes than allowed. -/
  | totalBytesBudget (found limit : Nat)
  /-- A field or payload beginning at `offset` had fewer bytes than required. -/
  | truncated (offset required found : Nat)
  /-- Header preflight requires exactly the fixed header byte count. -/
  | invalidHeaderSize (required found : Nat)
  /-- The first mismatching magic byte. -/
  | badMagic (offset : Nat) (expected found : UInt8)
  /-- The encoded schema version is not supported. -/
  | unsupportedVersion (offset : Nat) (found : UInt16)
  /-- The encoded payload-kind code is not assigned. -/
  | unsupportedKind (offset : Nat) (found : UInt16)
  /-- Adding the fixed header to the declared length would overflow `UInt64`. -/
  | payloadLengthOverflow (offset : Nat) (declared : UInt64)
  /-- An encoder input length cannot be represented by the wire's `UInt64` field. -/
  | payloadLengthUnrepresentable (offset required : Nat)
  /-- The declared payload exceeds the caller's payload budget. -/
  | payloadBytesBudget (offset required limit : Nat)
  /-- Bytes remain after the exact declared payload extent. -/
  | trailingBytes (offset count : Nat)
  /-- The stored checksum does not equal the checksum recomputed from the bytes. -/
  | checksumMismatch (offset : Nat) (stored computed : UInt64)
  /-- Complete bytes do not retain the exact header accepted by a prepared preflight. -/
  | preparedHeaderMismatch (offset : Nat) (expected found : UInt8)
  /-- A checked envelope has a different payload family from the caller's expectation. -/
  | expectedKindMismatch (offset : Nat) (expected found : PayloadKind)
  /-- A checked envelope has a different feature-schema fingerprint. -/
  | expectedFeatureFingerprintMismatch (offset : Nat)
      (expected found : FeatureFingerprint)
  /-- A checked envelope has a different tokenizer-profile fingerprint. -/
  | expectedTokenizerFingerprintMismatch (offset : Nat)
      (expected found : TokenizerFingerprint)
  deriving Repr, DecidableEq, BEq, Inhabited

namespace LittleEndian

/-- Append one exact byte. -/
@[inline] def appendUInt8 (bytes : ByteArray) (value : UInt8) : ByteArray :=
  bytes.push value

/-- Read one exact byte when `offset` is in bounds. -/
@[inline] def readUInt8? (bytes : ByteArray) (offset : Nat) : Option UInt8 :=
  if offset < bytes.size then some (bytes.get! offset) else none

/-- Append a `UInt16` in least-significant-byte-first order. -/
@[inline] def appendUInt16 (bytes : ByteArray) (value : UInt16) : ByteArray :=
  (bytes.push value.toUInt8).push (value >>> 8).toUInt8

/-- Read a little-endian `UInt16` when two bytes remain at `offset`. -/
@[inline] def readUInt16? (bytes : ByteArray) (offset : Nat) : Option UInt16 :=
  if offset + 2 ≤ bytes.size then
    let low := (bytes.get! offset).toUInt16
    let high := (bytes.get! (offset + 1)).toUInt16
    some (low ||| (high <<< 8))
  else
    none

/-- Append a `UInt32` in least-significant-byte-first order. -/
@[inline] def appendUInt32 (bytes : ByteArray) (value : UInt32) : ByteArray :=
  let bytes := bytes.push value.toUInt8
  let bytes := bytes.push (value >>> 8).toUInt8
  let bytes := bytes.push (value >>> 16).toUInt8
  bytes.push (value >>> 24).toUInt8

/-- Read a little-endian `UInt32` when four bytes remain at `offset`. -/
@[inline] def readUInt32? (bytes : ByteArray) (offset : Nat) : Option UInt32 :=
  if offset + 4 ≤ bytes.size then
    let b0 := (bytes.get! offset).toUInt32
    let b1 := (bytes.get! (offset + 1)).toUInt32
    let b2 := (bytes.get! (offset + 2)).toUInt32
    let b3 := (bytes.get! (offset + 3)).toUInt32
    some (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
  else
    none

/-- Append a `UInt64` in least-significant-byte-first order. -/
@[inline] def appendUInt64 (bytes : ByteArray) (value : UInt64) : ByteArray :=
  let bytes := bytes.push value.toUInt8
  let bytes := bytes.push (value >>> 8).toUInt8
  let bytes := bytes.push (value >>> 16).toUInt8
  let bytes := bytes.push (value >>> 24).toUInt8
  let bytes := bytes.push (value >>> 32).toUInt8
  let bytes := bytes.push (value >>> 40).toUInt8
  let bytes := bytes.push (value >>> 48).toUInt8
  bytes.push (value >>> 56).toUInt8

/-- Read a little-endian `UInt64` when eight bytes remain at `offset`. -/
@[inline] def readUInt64? (bytes : ByteArray) (offset : Nat) : Option UInt64 :=
  if offset + 8 ≤ bytes.size then
    let b0 := (bytes.get! offset).toUInt64
    let b1 := (bytes.get! (offset + 1)).toUInt64
    let b2 := (bytes.get! (offset + 2)).toUInt64
    let b3 := (bytes.get! (offset + 3)).toUInt64
    let b4 := (bytes.get! (offset + 4)).toUInt64
    let b5 := (bytes.get! (offset + 5)).toUInt64
    let b6 := (bytes.get! (offset + 6)).toUInt64
    let b7 := (bytes.get! (offset + 7)).toUInt64
    some (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
      (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56))
  else
    none

end LittleEndian

/-- FNV-1a's fixed 64-bit offset basis. -/
private def fnvOffsetBasis : UInt64 := 14_695_981_039_346_656_037

/-- FNV-1a's fixed 64-bit prime. -/
private def fnvPrime : UInt64 := 1_099_511_628_211

/-- Update a 64-bit FNV-1a state with a byte, using defined `UInt64` wraparound. -/
@[inline] private def checksumByte (state : UInt64) (byte : UInt8) : UInt64 :=
  (state ^^^ byte.toUInt64) * fnvPrime

/-- Fold one checked byte range into an existing checksum state without allocating a slice. -/
private def checksumRange (bytes : ByteArray) (start stop : Nat) (initial : UInt64) : UInt64 :=
  Id.run do
    let mut state := initial
    for index in [start:stop] do
      state := checksumByte state (bytes.get! index)
    return state

/--
Compute the deterministic 64-bit FNV-1a checksum over `headerPrefix` followed by `payload`.

This function is not cryptographically secure and must not be used for authentication.
-/
def checksum (headerPrefix payload : ByteArray) : UInt64 :=
  let afterPrefix := checksumRange headerPrefix 0 headerPrefix.size fnvOffsetBasis
  checksumRange payload 0 payload.size afterPrefix

/--
An artifact whose complete envelope, resource budgets, exact length, and checksum were checked.

The constructor is private so callers can obtain this type only through this module's decoders.
-/
structure Checked where
  private mk ::
  /-- Validated typed header metadata. -/
  metadata : Metadata
  /-- Exact uninterpreted payload as a zero-copy slice of the validated envelope. -/
  payload : ByteSlice

namespace Checked

/-- Copy the validated payload into a standalone byte array when ownership requires it. -/
@[inline] def copyPayload (checked : Checked) : ByteArray :=
  checked.payload.toByteArray

end Checked

/-- Largest payload length whose sum with the fixed header is representable as `UInt64`. -/
private def maxAddablePayloadLength : UInt64 :=
  0xffffffffffffffff - UInt64.ofNat Layout.payloadOffset

private def encodeUnchecked (metadata : Metadata) (payload : ByteArray) : ByteArray :=
  let capacity := Layout.headerSize + payload.size
  let header := ByteArray.emptyWithCapacity capacity ++ magic
  let header := LittleEndian.appendUInt16 header schemaVersion
  let header := LittleEndian.appendUInt16 header metadata.kind.code
  let header := LittleEndian.appendUInt64 header metadata.featureFingerprint.bits
  let header := LittleEndian.appendUInt64 header metadata.tokenizerFingerprint.bits
  let header := LittleEndian.appendUInt64 header (UInt64.ofNat payload.size)
  let storedChecksum := checksum header payload
  let header := LittleEndian.appendUInt64 header storedChecksum
  header ++ payload

/--
Check a prospective encoded payload length before any envelope allocation.

The returned size is the exact header-plus-payload allocation. Representability is checked before
resource budgets so every impossible wire length has a stable diagnostic.
-/
def preflightEncodeWith (config : Config) (payloadBytes : Nat) : Except Error Nat := do
  let maxUInt64 := (0xffffffffffffffff : UInt64).toNat
  if maxUInt64 < payloadBytes then
    throw <| .payloadLengthUnrepresentable Layout.payloadLengthOffset payloadBytes
  let declared := UInt64.ofNat payloadBytes
  if maxAddablePayloadLength < declared then
    throw <| .payloadLengthOverflow Layout.payloadLengthOffset declared
  if config.maxPayloadBytes < payloadBytes then
    throw <| .payloadBytesBudget Layout.payloadLengthOffset payloadBytes config.maxPayloadBytes
  let total := Layout.headerSize + payloadBytes
  if config.maxTotalBytes < total then
    throw <| .totalBytesBudget total config.maxTotalBytes
  return total

/-- Encode one artifact after exact representability and allocation-budget checks. -/
def encodeWith (config : Config) (metadata : Metadata) (payload : ByteArray) :
    Except Error ByteArray := do
  let _ ← preflightEncodeWith config payload.size
  return encodeUnchecked metadata payload

/--
Encode an artifact without allocation limits.

This convenience function is intended for already trusted in-memory payloads. Use `encodeWith`
when payload size is not already controlled by the caller.
-/
def encode (metadata : Metadata) (payload : ByteArray) : ByteArray :=
  encodeUnchecked metadata payload

/-- Return the first mismatching magic byte, if any. -/
private def validateMagic (bytes : ByteArray) : Except Error Unit := do
  for index in [0:magic.size] do
    let expected := magic.get! index
    let found := bytes.get! index
    if found != expected then
      throw <| .badMagic index expected found

/-- Maximum payload bytes hashed between two caller-supplied checksum polls. -/
def checksumChunkBytes : Nat := 65_536

private structure HeaderData where
  metadata : Metadata
  payloadBytes : Nat
  total : Nat
  storedChecksum : UInt64

/--
A validated fixed header prepared for a bounded one-handle payload read.

The private constructor binds parsed fields and resource limits to the retained exact 44-byte
snapshot. `totalBytes` tells a loader the complete envelope extent to read before finishing.
-/
structure PreparedHeader where
  private mk ::
  /-- Exact fixed header snapshot accepted by preflight. -/
  header : ByteArray
  /-- Structurally validated typed metadata; checksum validation occurs when finishing. -/
  metadata : Metadata
  /-- Exact declared payload bytes accepted by the payload budget. -/
  payloadBytes : Nat
  /-- Exact header-plus-payload extent accepted by the total budget. -/
  totalBytes : Nat
  /-- Stored checksum retained for the finishing pass. -/
  storedChecksum : UInt64

private def parseHeaderWith (config : Config) (bytes : ByteArray) :
    Except Error HeaderData := do
  if bytes.size < Layout.headerSize then
    throw <| .truncated 0 Layout.headerSize bytes.size
  validateMagic bytes
  let some version := LittleEndian.readUInt16? bytes Layout.versionOffset
    | throw <| .truncated Layout.versionOffset 2 (bytes.size - Layout.versionOffset)
  if version != schemaVersion then
    throw <| .unsupportedVersion Layout.versionOffset version
  let some kindCode := LittleEndian.readUInt16? bytes Layout.kindOffset
    | throw <| .truncated Layout.kindOffset 2 (bytes.size - Layout.kindOffset)
  let some kind := PayloadKind.ofCode? kindCode
    | throw <| .unsupportedKind Layout.kindOffset kindCode
  let some featureBits := LittleEndian.readUInt64? bytes Layout.featureFingerprintOffset
    | throw <| .truncated Layout.featureFingerprintOffset 8
        (bytes.size - Layout.featureFingerprintOffset)
  let some tokenizerBits := LittleEndian.readUInt64? bytes Layout.tokenizerFingerprintOffset
    | throw <| .truncated Layout.tokenizerFingerprintOffset 8
        (bytes.size - Layout.tokenizerFingerprintOffset)
  let some declared := LittleEndian.readUInt64? bytes Layout.payloadLengthOffset
    | throw <| .truncated Layout.payloadLengthOffset 8
        (bytes.size - Layout.payloadLengthOffset)
  if maxAddablePayloadLength < declared then
    throw <| .payloadLengthOverflow Layout.payloadLengthOffset declared
  let payloadBytes := declared.toNat
  if config.maxPayloadBytes < payloadBytes then
    throw <| .payloadBytesBudget Layout.payloadLengthOffset payloadBytes config.maxPayloadBytes
  let total := Layout.payloadOffset + payloadBytes
  if config.maxTotalBytes < total then
    throw <| .totalBytesBudget total config.maxTotalBytes
  let some storedChecksum := LittleEndian.readUInt64? bytes Layout.checksumOffset
    | throw <| .truncated Layout.checksumOffset 8 (bytes.size - Layout.checksumOffset)
  let metadata : Metadata :=
    { kind
      featureFingerprint := ⟨featureBits⟩
      tokenizerFingerprint := ⟨tokenizerBits⟩ }
  return ⟨metadata, payloadBytes, total, storedChecksum⟩

private def checkExtent (header : HeaderData) (bytes : ByteArray) : Except Error Unit := do
  if bytes.size < header.total then
    throw <| .truncated Layout.payloadOffset header.payloadBytes
      (bytes.size - Layout.payloadOffset)
  if header.total < bytes.size then
    throw <| .trailingBytes header.total (bytes.size - header.total)

private def decodeHeaderWith (config : Config) (bytes : ByteArray) :
    Except Error HeaderData := do
  if config.maxTotalBytes < bytes.size then
    throw <| .totalBytesBudget bytes.size config.maxTotalBytes
  let header ← parseHeaderWith config bytes
  checkExtent header bytes
  return header

/--
Validate exactly one fixed header and expose its bounded complete-envelope extent.

The returned value retains the header snapshot. Prepared finishing APIs reject complete bytes whose
first 44 bytes differ, preventing a preflight result from being reused with another envelope.
-/
def prepareHeaderWith (config : Config) (header : ByteArray) : Except Error PreparedHeader := do
  if header.size != Layout.headerSize then
    throw <| .invalidHeaderSize Layout.headerSize header.size
  let parsed ← parseHeaderWith config header
  return .mk header parsed.metadata parsed.payloadBytes parsed.total parsed.storedChecksum

/-- Prepare an exact fixed header under default production limits. -/
@[inline] def prepareHeader (header : ByteArray) : Except Error PreparedHeader :=
  prepareHeaderWith .default header

private def dataOfPrepared (prepared : PreparedHeader) : HeaderData :=
  ⟨prepared.metadata, prepared.payloadBytes, prepared.totalBytes, prepared.storedChecksum⟩

private def checkPreparedBinding (prepared : PreparedHeader) (bytes : ByteArray) :
    Except Error Unit := do
  for index in [0:Layout.headerSize] do
    let expected := prepared.header.get! index
    let found := bytes.get! index
    if found != expected then
      throw <| .preparedHeaderMismatch index expected found

private def checkExpected (expected found : Metadata) : Except Error Unit := do
  if expected.kind != found.kind then
    throw <| .expectedKindMismatch Layout.kindOffset expected.kind found.kind
  if expected.featureFingerprint != found.featureFingerprint then
    throw <| .expectedFeatureFingerprintMismatch Layout.featureFingerprintOffset
      expected.featureFingerprint found.featureFingerprint
  if expected.tokenizerFingerprint != found.tokenizerFingerprint then
    throw <| .expectedTokenizerFingerprintMismatch Layout.tokenizerFingerprintOffset
      expected.tokenizerFingerprint found.tokenizerFingerprint

private def encodedChecksumWithPoll [Monad m] (bytes : ByteArray) (total : Nat)
    (poll : m Unit) : m UInt64 := do
  poll
  let mut state := checksumRange bytes 0 Layout.checksumOffset fnvOffsetBasis
  let mut start := Layout.payloadOffset
  while start < total do
    let stop := min (start + checksumChunkBytes) total
    state := checksumRange bytes start stop state
    start := stop
    if start < total then
      poll
  return state

private def finishDataWithPoll [Monad m] (header : HeaderData) (expected : Option Metadata)
    (bytes : ByteArray) (poll : m Unit) : ExceptT Error m Checked := do
  let computedChecksum ← liftM <| encodedChecksumWithPoll bytes header.total poll
  if header.storedChecksum != computedChecksum then
    throw <| .checksumMismatch Layout.checksumOffset header.storedChecksum computedChecksum
  match expected with
  | some expected =>
      match checkExpected expected header.metadata with
      | .ok () => pure ()
      | .error cause => throw cause
  | none => pure ()
  return .mk header.metadata (bytes.toByteSlice Layout.payloadOffset header.total)

private def decodeCoreWithPoll [Monad m] (config : Config) (expected : Option Metadata)
    (bytes : ByteArray) (poll : m Unit) : ExceptT Error m Checked := do
  let header ← match decodeHeaderWith config bytes with
    | .ok header => pure header
    | .error cause => throw cause
  finishDataWithPoll header expected bytes poll

/--
Decode an artifact while polling once before checksum work and between fixed payload chunks.

Structural checks precede polling. The checksum visits every covered byte exactly once; each
uninterrupted payload segment contains at most `checksumChunkBytes` bytes.
-/
def decodeWithPoll [Monad m] (config : Config) (bytes : ByteArray) (poll : m Unit) :
    ExceptT Error m Checked :=
  decodeCoreWithPoll config none bytes poll

/--
Decode and certify expected kind and fingerprints with chunked caller-supplied polling.

Metadata mismatches are rejected only after structural and checksum validation.
-/
def decodeExpectedWithPoll [Monad m] (config : Config) (expected : Metadata)
    (bytes : ByteArray) (poll : m Unit) : ExceptT Error m Checked :=
  decodeCoreWithPoll config (some expected) bytes poll

/--
Finish a prepared header against its exact complete envelope with chunked polling.

The complete extent and retained 44-byte snapshot are checked before checksum work. No wire field is
parsed a second time, and the returned payload remains a zero-copy slice of `bytes`.
-/
def finishPreparedWithPoll [Monad m] (prepared : PreparedHeader) (bytes : ByteArray)
    (poll : m Unit) : ExceptT Error m Checked := do
  let header := dataOfPrepared prepared
  match checkExtent header bytes with
  | .ok () => pure ()
  | .error cause => throw cause
  match checkPreparedBinding prepared bytes with
  | .ok () => pure ()
  | .error cause => throw cause
  finishDataWithPoll header none bytes poll

/-- Finish a prepared header and certify expected metadata with chunked polling. -/
def finishPreparedExpectedWithPoll [Monad m] (prepared : PreparedHeader)
    (expected : Metadata) (bytes : ByteArray) (poll : m Unit) : ExceptT Error m Checked := do
  let header := dataOfPrepared prepared
  match checkExtent header bytes with
  | .ok () => pure ()
  | .error cause => throw cause
  match checkPreparedBinding prepared bytes with
  | .ok () => pure ()
  | .error cause => throw cause
  finishDataWithPoll header (some expected) bytes poll

/-- Finish a prepared header with a no-op checksum poll. -/
def finishPrepared (prepared : PreparedHeader) (bytes : ByteArray) : Except Error Checked :=
  Id.run <| (finishPreparedWithPoll (m := Id) prepared bytes (pure ())).run

/-- Finish a prepared header, certify expected metadata, and use a no-op checksum poll. -/
def finishPreparedExpected (prepared : PreparedHeader) (expected : Metadata)
    (bytes : ByteArray) : Except Error Checked :=
  Id.run <|
    (finishPreparedExpectedWithPoll (m := Id) prepared expected bytes (pure ())).run

/--
Decode an artifact under explicit total-byte and payload-byte budgets.

No payload buffer is allocated or copied. The checked result retains a `ByteSlice` into the input
`ByteArray`, which is itself owned and allocated by the caller.
-/
def decodeWith (config : Config) (bytes : ByteArray) : Except Error Checked := do
  Id.run <| (decodeWithPoll (m := Id) config bytes (pure ())).run

/-- Decode and certify expected metadata under explicit production resource limits. -/
def decodeExpectedWith (config : Config) (expected : Metadata) (bytes : ByteArray) :
    Except Error Checked :=
  Id.run <| (decodeExpectedWithPoll (m := Id) config expected bytes (pure ())).run

/-- Decode an artifact under production resource limits. -/
@[inline] def decode (bytes : ByteArray) : Except Error Checked :=
  decodeWith .default bytes

/-- Decode and certify expected metadata under default production resource limits. -/
@[inline] def decodeExpected (expected : Metadata) (bytes : ByteArray) : Except Error Checked :=
  decodeExpectedWith .default expected bytes

end Nlp.Model.Artifact
