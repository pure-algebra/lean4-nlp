import Nlp.Model.Artifact

namespace NlpTests.Model.Artifact

open Nlp.Model.Artifact

private def sampleMetadata : Metadata :=
  { kind := .crfNer
    featureFingerprint := ⟨0x0123456789abcdef⟩
    tokenizerFingerprint := ⟨0xfedcba9876543210⟩ }

private def samplePayload : ByteArray :=
  [0x00, 0x01, 0x7f, 0x80, 0xfe, 0xff].toByteArray

private def sampleEnvelope : ByteArray :=
  encode sampleMetadata samplePayload

private def sampleHeader : ByteArray :=
  sampleEnvelope.extract 0 Layout.headerSize

#guard magic == [0x4c, 0x34, 0x4e, 0x4c, 0x50, 0x41, 0x52, 0x54].toByteArray
#guard schemaVersion == 1
#guard PayloadKind.crfNer.code == 1
#guard Layout.versionOffset == 8
#guard Layout.kindOffset == 10
#guard Layout.featureFingerprintOffset == 12
#guard Layout.tokenizerFingerprintOffset == 20
#guard Layout.payloadLengthOffset == 28
#guard Layout.checksumOffset == 36
#guard Layout.payloadOffset == 44
#guard Layout.headerSize == 44

private def replaceBytes (bytes : ByteArray) (offset : Nat) (replacement : ByteArray) :
    ByteArray :=
  replacement.copySlice 0 bytes offset replacement.size

private def replaceUInt16 (bytes : ByteArray) (offset : Nat) (value : UInt16) : ByteArray :=
  replaceBytes bytes offset (LittleEndian.appendUInt16 {} value)

private def replaceUInt64 (bytes : ByteArray) (offset : Nat) (value : UInt64) : ByteArray :=
  replaceBytes bytes offset (LittleEndian.appendUInt64 {} value)

private def roundTrip : Bool :=
  match decode sampleEnvelope with
  | .ok checked =>
    checked.metadata == sampleMetadata && checked.payload == samplePayload.toByteSlice &&
      encode checked.metadata checked.copyPayload == sampleEnvelope
  | .error _ => false

#guard roundTrip

private def expectedRoundTrip : Bool :=
  match decodeExpected sampleMetadata sampleEnvelope with
  | .ok checked =>
      checked.metadata == sampleMetadata && checked.payload == samplePayload.toByteSlice
  | .error _ => false

#guard expectedRoundTrip

private def expectedFeatureMismatch : Bool :=
  let expected : Metadata :=
    { sampleMetadata with featureFingerprint := ⟨sampleMetadata.featureFingerprint.bits + 1⟩ }
  match decodeExpected expected sampleEnvelope with
  | .error (.expectedFeatureFingerprintMismatch offset wanted found) =>
    offset == Layout.featureFingerprintOffset && wanted == expected.featureFingerprint &&
      found == sampleMetadata.featureFingerprint
  | _ => false

#guard expectedFeatureMismatch

private def expectedTokenizerMismatch : Bool :=
  let expected : Metadata :=
    { sampleMetadata with tokenizerFingerprint := ⟨sampleMetadata.tokenizerFingerprint.bits + 1⟩ }
  match decodeExpected expected sampleEnvelope with
  | .error (.expectedTokenizerFingerprintMismatch offset wanted found) =>
    offset == Layout.tokenizerFingerprintOffset && wanted == expected.tokenizerFingerprint &&
      found == sampleMetadata.tokenizerFingerprint
  | _ => false

#guard expectedTokenizerMismatch

private def emptyRoundTrip : Bool :=
  let envelope := encode sampleMetadata {}
  match decode envelope with
  | .ok checked => checked.metadata == sampleMetadata && checked.payload.size == 0
  | .error _ => false

#guard emptyRoundTrip

/- Exact byte order and boundary behavior for every fixed-width unsigned helper. -/
#guard LittleEndian.appendUInt8 {} 0 == [0].toByteArray
#guard LittleEndian.appendUInt8 {} 0xff == [0xff].toByteArray
#guard LittleEndian.readUInt8? [0].toByteArray 0 == some 0
#guard LittleEndian.readUInt8? [0xff].toByteArray 0 == some 0xff
#guard LittleEndian.readUInt8? {} 0 == none

#guard LittleEndian.appendUInt16 {} 0 == [0, 0].toByteArray
#guard LittleEndian.appendUInt16 {} 0xffff == [0xff, 0xff].toByteArray
#guard LittleEndian.appendUInt16 {} 0x1234 == [0x34, 0x12].toByteArray
#guard LittleEndian.readUInt16? (LittleEndian.appendUInt16 {} 0) 0 == some 0
#guard LittleEndian.readUInt16? (LittleEndian.appendUInt16 {} 0xffff) 0 == some 0xffff
#guard LittleEndian.readUInt16? [0x99, 0x34, 0x12].toByteArray 1 == some 0x1234
#guard LittleEndian.readUInt16? [0x34].toByteArray 0 == none

#guard LittleEndian.appendUInt32 {} 0 == [0, 0, 0, 0].toByteArray
#guard LittleEndian.appendUInt32 {} 0xffffffff == [0xff, 0xff, 0xff, 0xff].toByteArray
#guard LittleEndian.appendUInt32 {} 0x12345678 == [0x78, 0x56, 0x34, 0x12].toByteArray
#guard LittleEndian.readUInt32? (LittleEndian.appendUInt32 {} 0) 0 == some 0
#guard LittleEndian.readUInt32? (LittleEndian.appendUInt32 {} 0xffffffff) 0 == some 0xffffffff
#guard LittleEndian.readUInt32? [0x99, 0x78, 0x56, 0x34, 0x12].toByteArray 1 ==
  some 0x12345678
#guard LittleEndian.readUInt32? [0x78, 0x56, 0x34].toByteArray 0 == none

#guard LittleEndian.appendUInt64 {} 0 == [0, 0, 0, 0, 0, 0, 0, 0].toByteArray
#guard LittleEndian.appendUInt64 {} 0xffffffffffffffff ==
  [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff].toByteArray
#guard LittleEndian.appendUInt64 {} 0x0123456789abcdef ==
  [0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01].toByteArray
#guard LittleEndian.readUInt64? (LittleEndian.appendUInt64 {} 0) 0 == some 0
#guard LittleEndian.readUInt64? (LittleEndian.appendUInt64 {} 0xffffffffffffffff) 0 ==
  some 0xffffffffffffffff
#guard LittleEndian.readUInt64?
    [0x99, 0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01].toByteArray 1 ==
  some 0x0123456789abcdef
#guard LittleEndian.readUInt64?
    [0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23].toByteArray 0 == none

/- Standard FNV-1a vectors pin the deterministic, wrapping checksum implementation. -/
#guard checksum {} {} == 0xcbf29ce484222325
#guard checksum {} [0x61].toByteArray == 0xaf63dc4c8601ec8c
#guard checksum {} [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72].toByteArray ==
  0x85944171f73967e8
#guard checksum [0x66, 0x6f, 0x6f].toByteArray [0x62, 0x61, 0x72].toByteArray ==
  checksum {} [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72].toByteArray

private def exactLayout : Bool :=
  let stored := LittleEndian.readUInt64? sampleEnvelope Layout.checksumOffset
  let headerPrefix := sampleEnvelope.extract 0 Layout.checksumOffset
  stored == some (checksum headerPrefix samplePayload) &&
    sampleEnvelope.size == Layout.headerSize + samplePayload.size &&
    sampleEnvelope.extract 0 magic.size == magic &&
    LittleEndian.readUInt16? sampleEnvelope Layout.versionOffset == some schemaVersion &&
    LittleEndian.readUInt16? sampleEnvelope Layout.kindOffset == some PayloadKind.crfNer.code &&
    LittleEndian.readUInt64? sampleEnvelope Layout.featureFingerprintOffset ==
      some sampleMetadata.featureFingerprint.bits &&
    LittleEndian.readUInt64? sampleEnvelope Layout.tokenizerFingerprintOffset ==
      some sampleMetadata.tokenizerFingerprint.bits &&
    LittleEndian.readUInt64? sampleEnvelope Layout.payloadLengthOffset ==
      some (UInt64.ofNat samplePayload.size)

#guard exactLayout

private def exactBudgets : Bool :=
  let config : Config :=
    { maxTotalBytes := sampleEnvelope.size
      maxPayloadBytes := samplePayload.size }
  match decodeWith config sampleEnvelope with
  | .ok checked => checked.payload == samplePayload.toByteSlice
  | .error _ => false

#guard exactBudgets

private def preparedRoundTrip : Bool :=
  let config : Config :=
    { maxTotalBytes := sampleEnvelope.size
      maxPayloadBytes := samplePayload.size }
  match prepareHeaderWith config sampleHeader with
  | .ok prepared =>
      prepared.header == sampleHeader && prepared.metadata == sampleMetadata &&
        prepared.payloadBytes == samplePayload.size &&
        prepared.totalBytes == sampleEnvelope.size &&
        match finishPreparedExpected prepared sampleMetadata sampleEnvelope with
        | .ok checked => checked.payload == samplePayload.toByteSlice
        | .error _ => false
  | .error _ => false

#guard preparedRoundTrip

private def preparedHeaderOneShort : Bool :=
  let header := sampleHeader.extract 0 (Layout.headerSize - 1)
  match prepareHeader header with
  | .error (.invalidHeaderSize required found) =>
      required == Layout.headerSize && found == Layout.headerSize - 1
  | _ => false

#guard preparedHeaderOneShort

private def preparedHeaderOneLong : Bool :=
  match prepareHeader (sampleHeader.push 0) with
  | .error (.invalidHeaderSize required found) =>
      required == Layout.headerSize && found == Layout.headerSize + 1
  | _ => false

#guard preparedHeaderOneLong

private def preparedTotalBudgetOneShort : Bool :=
  let limit := sampleEnvelope.size - 1
  let config : Config :=
    { maxTotalBytes := limit
      maxPayloadBytes := samplePayload.size }
  match prepareHeaderWith config sampleHeader with
  | .error (.totalBytesBudget required reportedLimit) =>
      required == sampleEnvelope.size && reportedLimit == limit
  | _ => false

#guard preparedTotalBudgetOneShort

private def preparedPayloadBudgetOneShort : Bool :=
  let limit := samplePayload.size - 1
  let config : Config :=
    { maxTotalBytes := sampleEnvelope.size
      maxPayloadBytes := limit }
  match prepareHeaderWith config sampleHeader with
  | .error (.payloadBytesBudget offset required reportedLimit) =>
      offset == Layout.payloadLengthOffset && required == samplePayload.size &&
        reportedLimit == limit
  | _ => false

#guard preparedPayloadBudgetOneShort

private def preparedBindingMismatch : Bool :=
  match prepareHeader sampleHeader with
  | .ok prepared =>
      let offset := Layout.featureFingerprintOffset
      let expected := sampleEnvelope.get! offset
      let found := expected ^^^ 1
      match finishPrepared prepared (sampleEnvelope.set! offset found) with
      | .error (.preparedHeaderMismatch reportedOffset reportedExpected reportedFound) =>
          reportedOffset == offset && reportedExpected == expected && reportedFound == found
      | _ => false
  | .error _ => false

#guard preparedBindingMismatch

private def preparedTruncatedPayload : Bool :=
  match prepareHeader sampleHeader with
  | .ok prepared =>
      let bytes := sampleEnvelope.extract 0 (sampleEnvelope.size - 1)
      match finishPrepared prepared bytes with
      | .error (.truncated offset required found) =>
          offset == Layout.payloadOffset && required == samplePayload.size &&
            found == samplePayload.size - 1
      | _ => false
  | .error _ => false

#guard preparedTruncatedPayload

private def preparedTrailingByte : Bool :=
  match prepareHeader sampleHeader with
  | .ok prepared =>
      match finishPrepared prepared (sampleEnvelope.push 0) with
      | .error (.trailingBytes offset count) =>
          offset == sampleEnvelope.size && count == 1
      | _ => false
  | .error _ => false

#guard preparedTrailingByte

private def exactEncodeBudgets : Bool :=
  let config : Config :=
    { maxTotalBytes := sampleEnvelope.size
      maxPayloadBytes := samplePayload.size }
  match encodeWith config sampleMetadata samplePayload with
  | .ok encoded => encoded == sampleEnvelope
  | .error _ => false

#guard exactEncodeBudgets

private def encodeTotalBudgetOneShort : Bool :=
  let limit := sampleEnvelope.size - 1
  let config : Config :=
    { maxTotalBytes := limit
      maxPayloadBytes := samplePayload.size }
  match encodeWith config sampleMetadata samplePayload with
  | .error (.totalBytesBudget required reportedLimit) =>
    required == sampleEnvelope.size && reportedLimit == limit
  | _ => false

#guard encodeTotalBudgetOneShort

private def encodePayloadBudgetOneShort : Bool :=
  let limit := samplePayload.size - 1
  let config : Config :=
    { maxTotalBytes := sampleEnvelope.size
      maxPayloadBytes := limit }
  match encodeWith config sampleMetadata samplePayload with
  | .error (.payloadBytesBudget offset required reportedLimit) =>
    offset == Layout.payloadLengthOffset && required == samplePayload.size &&
      reportedLimit == limit
  | _ => false

#guard encodePayloadBudgetOneShort

private def decodedPayloadIsSlice : Bool :=
  match decode sampleEnvelope with
  | .ok checked =>
    checked.payload.start == Layout.payloadOffset &&
      checked.payload.stop == sampleEnvelope.size &&
      checked.payload.byteArray == sampleEnvelope
  | .error _ => false

#guard decodedPayloadIsSlice

private def totalBudgetOneShort : Bool :=
  let limit := sampleEnvelope.size - 1
  let config : Config :=
    { maxTotalBytes := limit
      maxPayloadBytes := samplePayload.size }
  match decodeWith config sampleEnvelope with
  | .error (.totalBytesBudget found reportedLimit) =>
    found == sampleEnvelope.size && reportedLimit == limit
  | _ => false

#guard totalBudgetOneShort

private def payloadBudgetOneShort : Bool :=
  let limit := samplePayload.size - 1
  let config : Config :=
    { maxTotalBytes := sampleEnvelope.size
      maxPayloadBytes := limit }
  match decodeWith config sampleEnvelope with
  | .error (.payloadBytesBudget offset required reportedLimit) =>
    offset == Layout.payloadLengthOffset && required == samplePayload.size &&
      reportedLimit == limit
  | _ => false

#guard payloadBudgetOneShort

private def truncatedHeader : Bool :=
  let bytes := sampleEnvelope.extract 0 (Layout.headerSize - 1)
  match decode bytes with
  | .error (.truncated offset required found) =>
    offset == 0 && required == Layout.headerSize && found == Layout.headerSize - 1
  | _ => false

#guard truncatedHeader

private def truncatedPayload : Bool :=
  let bytes := sampleEnvelope.extract 0 (sampleEnvelope.size - 1)
  match decode bytes with
  | .error (.truncated offset required found) =>
    offset == Layout.payloadOffset && required == samplePayload.size &&
      found == samplePayload.size - 1
  | _ => false

#guard truncatedPayload

private def badMagic : Bool :=
  let bytes := sampleEnvelope.set! 3 0
  match decode bytes with
  | .error (.badMagic offset expected found) =>
    offset == 3 && expected == magic.get! 3 && found == 0
  | _ => false

#guard badMagic

private def badVersion : Bool :=
  let bytes := replaceUInt16 sampleEnvelope Layout.versionOffset 2
  match decode bytes with
  | .error (.unsupportedVersion offset found) =>
    offset == Layout.versionOffset && found == 2
  | _ => false

#guard badVersion

private def badKind : Bool :=
  let bytes := replaceUInt16 sampleEnvelope Layout.kindOffset 0xffff
  match decode bytes with
  | .error (.unsupportedKind offset found) =>
    offset == Layout.kindOffset && found == 0xffff
  | _ => false

#guard badKind

private def payloadLengthOverflow : Bool :=
  let bytes := replaceUInt64 sampleEnvelope Layout.payloadLengthOffset 0xffffffffffffffff
  match decode bytes with
  | .error (.payloadLengthOverflow offset declared) =>
    offset == Layout.payloadLengthOffset && declared == 0xffffffffffffffff
  | _ => false

#guard payloadLengthOverflow

private def maximumNonoverflowingLength : UInt64 :=
  0xffffffffffffffff - UInt64.ofNat Layout.payloadOffset

private def maximumLengthReachesExtentCheck : Bool :=
  let bytes := replaceUInt64 (encode sampleMetadata {}) Layout.payloadLengthOffset
    maximumNonoverflowingLength
  let config : Config :=
    { maxTotalBytes := (0xffffffffffffffff : UInt64).toNat
      maxPayloadBytes := maximumNonoverflowingLength.toNat }
  match decodeWith config bytes with
  | .error (.truncated offset required found) =>
    offset == Layout.payloadOffset && required == maximumNonoverflowingLength.toNat && found == 0
  | _ => false

#guard maximumLengthReachesExtentCheck

private def maximumEncodeLengthPreflights : Bool :=
  let maxUInt64 := (0xffffffffffffffff : UInt64).toNat
  let maximum := maxUInt64 - Layout.payloadOffset
  let config : Config :=
    { maxTotalBytes := maxUInt64
      maxPayloadBytes := maximum }
  match preflightEncodeWith config maximum with
  | .ok total => total == maxUInt64
  | .error _ => false

#guard maximumEncodeLengthPreflights

private def encodeLengthAdditionOverflow : Bool :=
  let maximum : UInt64 :=
    0xffffffffffffffff - UInt64.ofNat Layout.payloadOffset
  let required := maximum.toNat + 1
  let config : Config :=
    { maxTotalBytes := (0xffffffffffffffff : UInt64).toNat
      maxPayloadBytes := required }
  match preflightEncodeWith config required with
  | .error (.payloadLengthOverflow offset declared) =>
    offset == Layout.payloadLengthOffset && declared == maximum + 1
  | _ => false

#guard encodeLengthAdditionOverflow

private def encodeLengthUnrepresentable : Bool :=
  let required := (0xffffffffffffffff : UInt64).toNat + 1
  let config : Config :=
    { maxTotalBytes := required
      maxPayloadBytes := required }
  match preflightEncodeWith config required with
  | .error (.payloadLengthUnrepresentable offset reported) =>
    offset == Layout.payloadLengthOffset && reported == required
  | _ => false

#guard encodeLengthUnrepresentable

private def declaredTotalBudget : Bool :=
  let bytes := replaceUInt64 (encode sampleMetadata {}) Layout.payloadLengthOffset 1
  let config : Config :=
    { maxTotalBytes := bytes.size
      maxPayloadBytes := 1 }
  match decodeWith config bytes with
  | .error (.totalBytesBudget required limit) =>
    required == Layout.headerSize + 1 && limit == Layout.headerSize
  | _ => false

#guard declaredTotalBudget

private def declaredLengthOneTooLarge : Bool :=
  let bytes := replaceUInt64 sampleEnvelope Layout.payloadLengthOffset
    (UInt64.ofNat (samplePayload.size + 1))
  match decode bytes with
  | .error (.truncated offset required found) =>
    offset == Layout.payloadOffset && required == samplePayload.size + 1 &&
      found == samplePayload.size
  | _ => false

#guard declaredLengthOneTooLarge

private def declaredLengthOneTooSmall : Bool :=
  let bytes := replaceUInt64 sampleEnvelope Layout.payloadLengthOffset
    (UInt64.ofNat (samplePayload.size - 1))
  match decode bytes with
  | .error (.trailingBytes offset count) =>
    offset == sampleEnvelope.size - 1 && count == 1
  | _ => false

#guard declaredLengthOneTooSmall

private def trailingByte : Bool :=
  let bytes := sampleEnvelope ++ [0].toByteArray
  match decode bytes with
  | .error (.trailingBytes offset count) =>
    offset == sampleEnvelope.size && count == 1
  | _ => false

#guard trailingByte

private def payloadChecksumMismatch : Bool :=
  let bytes := sampleEnvelope.set! Layout.payloadOffset 0xff
  match decode bytes with
  | .error (.checksumMismatch offset stored computed) =>
    offset == Layout.checksumOffset && stored != computed
  | _ => false

#guard payloadChecksumMismatch

private def metadataChecksumMismatch : Bool :=
  let bytes := sampleEnvelope.set! Layout.featureFingerprintOffset 0xff
  match decode bytes with
  | .error (.checksumMismatch offset stored computed) =>
    offset == Layout.checksumOffset && stored != computed
  | _ => false

#guard metadataChecksumMismatch

private def checksumPrecedesExpectedMismatch : Bool :=
  let bytes := sampleEnvelope.set! Layout.featureFingerprintOffset 0xff
  match decodeExpected sampleMetadata bytes with
  | .error (.checksumMismatch offset stored computed) =>
    offset == Layout.checksumOffset && stored != computed
  | _ => false

#guard checksumPrecedesExpectedMismatch

private def tokenizerChecksumMismatch : Bool :=
  let bytes := sampleEnvelope.set! Layout.tokenizerFingerprintOffset 0xff
  match decode bytes with
  | .error (.checksumMismatch offset stored computed) =>
    offset == Layout.checksumOffset && stored != computed
  | _ => false

#guard tokenizerChecksumMismatch

private def lengthChecksumMismatch : Bool :=
  let bytes := replaceUInt64 (encode sampleMetadata {}) Layout.payloadLengthOffset 1 ++
    [0x61].toByteArray
  match decode bytes with
  | .error (.checksumMismatch offset stored computed) =>
    offset == Layout.checksumOffset && stored != computed
  | _ => false

#guard lengthChecksumMismatch

private def storedChecksumMismatch : Bool :=
  let bytes := sampleEnvelope.set! Layout.checksumOffset
    (sampleEnvelope.get! Layout.checksumOffset ^^^ 1)
  match decode bytes with
  | .error (.checksumMismatch offset stored computed) =>
    offset == Layout.checksumOffset && stored != computed
  | _ => false

#guard storedChecksumMismatch

private def pollCount (payloadBytes : Nat) : Option Nat :=
  let payload := ByteArray.mk (Array.replicate payloadBytes 0x61)
  let envelope := encode sampleMetadata payload
  let poll : StateM Nat Unit := fun count ↦ ((), count + 1)
  let (result, count) :=
    (decodeExpectedWithPoll (m := StateM Nat) .default sampleMetadata envelope poll).run 0
  match result with
  | .ok checked => if checked.payload.size == payloadBytes then some count else none
  | .error _ => none

/- Poll once before checksum work, then once at every fixed payload-chunk boundary. -/
#guard pollCount 0 == some 1
#guard pollCount 1 == some 1
#guard pollCount checksumChunkBytes == some 1
#guard pollCount (checksumChunkBytes + 1) == some 2
#guard pollCount (2 * checksumChunkBytes) == some 2
#guard pollCount (2 * checksumChunkBytes + 1) == some 3

private def preparedPollCount (payloadBytes : Nat) : Option Nat :=
  let payload := ByteArray.mk (Array.replicate payloadBytes 0x61)
  let envelope := encode sampleMetadata payload
  let header := envelope.extract 0 Layout.headerSize
  match prepareHeader header with
  | .error _ => none
  | .ok prepared =>
      let poll : StateM Nat Unit := fun count ↦ ((), count + 1)
      let (result, count) :=
        (finishPreparedWithPoll (m := StateM Nat) prepared envelope poll).run 0
      match result with
      | .ok checked => if checked.payload.size == payloadBytes then some count else none
      | .error _ => none

#guard preparedPollCount (checksumChunkBytes + 1) == some 2

private def pollFailurePropagates : Bool :=
  let poll : Except String Unit := .error "cancelled"
  match (decodeWithPoll (m := Except String) .default sampleEnvelope poll).run with
  | .error "cancelled" => true
  | _ => false

#guard pollFailurePropagates

end NlpTests.Model.Artifact
