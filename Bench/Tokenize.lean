import Nlp

/-!
# Tokenization throughput benchmark

This standalone executable reports byte and token throughput for the pure scanner and the checked,
byte-weighted effectful corpus API. Baseline, web-heavy, and long near-miss fixtures exercise the
same complete-output checksums without imposing a machine-specific performance threshold.
-/

namespace TokenizeBenchmark

open Nlp Nlp.Tokenize

/-- One fully consumed tokenizer observation. -/
private structure Observation where
  checksum : UInt64
  tokens : Nat
  sentences : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Average wall time and an aggregate checksum keeping every repetition observable. -/
private structure Timing where
  nanos : Nat
  aggregate : UInt64

/-- One independently sized benchmark corpus and its repetition policy. -/
private structure Lane where
  name : String
  documents : Array String
  pureRepetitions : Nat
  effectRepetitions : Nat
  processRepetitions : Nat

/-- Deterministic fixed-width checksum mixer. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Mix a complete string and its exact UTF-8 byte width without allocating a character list. -/
@[inline] private def mixString (state : UInt64) (value : String) : UInt64 :=
  mix (mix state (UInt64.ofNat value.utf8ByteSize)) (hash value)

/-- Stable constructor ordinal for every public coarse token kind. -/
@[inline] private def kindCode : TokenKind → UInt64
  | .word => 0
  | .number => 1
  | .url => 2
  | .email => 3
  | .handle => 4
  | .hashtag => 5
  | .punctuation => 6
  | .symbol => 7
  | .newline => 8

/-- Repeat a fixture fragment without placing construction in a timed region. -/
private def repeatText (count : Nat) (text : String) : String :=
  String.join (List.replicate count text)

/-- General English and punctuation traffic retained as the baseline lane. -/
private def asciiParagraph : String :=
  "The U.S. team can't re-index 1,234.50 school-aged records. Another sentence follows! "

/-- Multilingual source alignment retained as the Unicode portion of the baseline lane. -/
private def unicodeParagraph : String :=
  "Unicode café 猫 😀 and e\u0301 remain source-aligned. ¿Otra oración? 你好世界。 "

/-- Web traffic with query strings, a Unicode path, emails, handles, and hashtags. -/
private def webParagraph : String :=
  "Open https://example.com/search?q=lean%204&lang=en#top, then " ++
    "https://example.org/路径/naïve?标签=值#片段. " ++
    "Mail first.last+bench@example-domain.org or ops_42@sub.example.net; " ++
    "ping @lean_lang and @_builder42 about #Lean4 and #形式化_验证. "

/-- Mixed non-web corpus used to retain the original throughput control. -/
private def baselineCorpus : Array String :=
  Array.ofFn (n := 2048) fun index ↦
    if index.val % 8 = 0 then repeatText 8 unicodeParagraph
    else if index.val % 3 = 0 then repeatText 4 asciiParagraph
    else asciiParagraph

/-- Corpus dominated by enabled web-token recognizers and Unicode boundaries. -/
private def webCorpus : Array String :=
  Array.ofFn (n := 1024) fun index ↦
    if index.val % 5 = 0 then repeatText 6 webParagraph
    else if index.val % 2 = 0 then repeatText 3 webParagraph
    else webParagraph

/--
One long last-accepting URL tail plus an almost-valid email.

The unmatched parentheses force a URL recognizer to retain an early accepting position after a
long scan. The one-letter email suffix forces complete validation with no accepted address. A
single-pass recognizer remains linear; repeated trimming or rescanning becomes visible here.
-/
private def nearMissDocument : String :=
  "https://example.com/stable" ++ repeatText 16384 "(" ++ " " ++
    repeatText 8192 "a." ++ "a@example.c end. "

/-- Adversarial corpus sized to keep repeated native benchmark runs practical. -/
private def nearMissCorpus : Array String :=
  Array.replicate 32 nearMissDocument

/-- All fixtures are built before any lane starts its timer. -/
private def lanes : Array Lane :=
  #[⟨"baseline", baselineCorpus, 5, 3, 2⟩,
    ⟨"web-heavy", webCorpus, 4, 2, 2⟩,
    ⟨"long web near-miss", nearMissCorpus, 3, 2, 2⟩]

/-- Total UTF-8 input size of one benchmark corpus. -/
private def corpusBytes (documents : Array String) : Nat :=
  documents.foldl (fun total text ↦ total + text.utf8ByteSize) 0

/-- Consume every pure token form, byte span, and coarse kind in source order. -/
private def observeTokenization (initial : UInt64)
    (tokenization : Tokenization) : Observation := Id.run do
  let mut checksum := mix initial (UInt64.ofNat tokenization.tokens.size)
  let mut tokens := 0
  for token in tokenization.tokens do
    checksum := mixString checksum token.original
    let span := token.span
    checksum := mix checksum (UInt64.ofNat span.b)
    checksum := mix checksum (UInt64.ofNat span.e)
    checksum := mix checksum (kindCode token.kind)
    tokens := tokens + 1
  return ⟨checksum, tokens, 0⟩

/-- Consume every document form, byte span, and sentence end in source order. -/
private def observeDoc (initial : UInt64) (document : Doc available) : Observation := Id.run do
  let mut checksum := mix initial (UInt64.ofNat document.forms.size)
  checksum := mix checksum (UInt64.ofNat document.spans.size)
  checksum := mix checksum (UInt64.ofNat document.sentEnd.size)
  for form in document.forms do
    checksum := mixString checksum form
  for span in document.spans do
    checksum := mix checksum (UInt64.ofNat span.b)
    checksum := mix checksum (UInt64.ofNat span.e)
  for sentenceEnd in document.sentEnd do
    checksum := mix checksum (UInt64.ofNat sentenceEnd)
  return ⟨checksum, document.forms.size, document.sentEnd.size⟩

/-- Fold complete pure scanner outputs into one stable corpus observation. -/
@[noinline] private def observePureTokens (tokenizer : Tokenizer)
    (documents : Array String) : Observation := Id.run do
  let mut result : Observation := ⟨mix 0 (UInt64.ofNat documents.size), 0, 0⟩
  for text in documents do
    let current := observeTokenization result.checksum (tokenizer.tokenize text)
    result := ⟨current.checksum, result.tokens + current.tokens, 0⟩
  return result

/-- Fold pure token-document projections into one stable corpus observation. -/
@[noinline] private def observePureTokenDocs (tokenizer : Tokenizer)
    (documents : Array String) : Observation := Id.run do
  let mut result : Observation := ⟨mix 0 (UInt64.ofNat documents.size), 0, 0⟩
  for text in documents do
    let current := observeDoc result.checksum (tokenizer.tokenizeDoc text)
    result := ⟨current.checksum, result.tokens + current.tokens, 0⟩
  return result

/-- Fold pure tokenize-and-split document projections into one stable corpus observation. -/
@[noinline] private def observePureProcess (tokenizer : Tokenizer)
    (documents : Array String) : Observation := Id.run do
  let mut result : Observation := ⟨mix 0 (UInt64.ofNat documents.size), 0, 0⟩
  for text in documents do
    let current := observeDoc result.checksum (tokenizer.process text)
    result :=
      ⟨current.checksum, result.tokens + current.tokens,
        result.sentences + current.sentences⟩
  return result

/-- Fold checked document columns into one stable corpus observation. -/
private def observeDocs (documents : Array (Doc available)) : Observation := Id.run do
  let mut result : Observation := ⟨mix 0 (UInt64.ofNat documents.size), 0, 0⟩
  for document in documents do
    let current := observeDoc result.checksum document
    result :=
      ⟨current.checksum, result.tokens + current.tokens,
        result.sentences + current.sentences⟩
  return result

/-- Run the checked token-only corpus API and retain its complete ordered output. -/
private def runTokenDocs (config : Nlp.Config) (tokenizer : Tokenizer)
    (documents : Array String) : IO (Array (Doc [.tokens])) := do
  match ← NLP.runIO config (NLP.tokenizeTextsWithMinBytes 65536 tokenizer documents) with
  | .ok output => return output
  | .error cause => throw <| IO.userError s!"tokenizer benchmark failed: {cause}"

/-- Run the checked tokenize-and-split corpus API and retain its complete ordered output. -/
private def runProcessDocs (config : Nlp.Config) (tokenizer : Tokenizer)
    (documents : Array String) : IO (Array (Doc [.sents, .tokens])) := do
  match ← NLP.runIO config
      (NLP.processTextsWithMinBytes 65536 tokenizer documents) with
  | .ok output => return output
  | .error cause => throw <| IO.userError s!"sentence benchmark failed: {cause}"

/-- Exact parity between checked token documents and their pure projections. -/
private def tokenDocParity (tokenizer : Tokenizer) (documents : Array String)
    (checked : Array (Doc [.tokens])) : Bool := Id.run do
  unless checked.size == documents.size do
    return false
  for index in [0:documents.size] do
    let expected := tokenizer.tokenizeDoc documents[index]!
    match checked[index]? with
    | none => return false
    | some actual =>
      unless actual.text == expected.text && actual.forms == expected.forms &&
          actual.spans == expected.spans do
        return false
  return true

/-- Exact parity between checked sentence documents and their pure projections. -/
private def processDocParity (tokenizer : Tokenizer) (documents : Array String)
    (checked : Array (Doc [.sents, .tokens])) : Bool := Id.run do
  unless checked.size == documents.size do
    return false
  for index in [0:documents.size] do
    let expected := tokenizer.process documents[index]!
    match checked[index]? with
    | none => return false
    | some actual =>
      unless actual.text == expected.text && actual.forms == expected.forms &&
          actual.spans == expected.spans && actual.sentEnd == expected.sentEnd do
        return false
  return true

/-- Observe one checked token-only run while forcing all public columns. -/
private def observeEffectTokens (config : Nlp.Config) (tokenizer : Tokenizer)
    (documents : Array String) : IO Observation := do
  return observeDocs (← runTokenDocs config tokenizer documents)

/-- Observe one checked tokenize-and-split run while forcing all public columns. -/
private def observeEffectProcess (config : Nlp.Config) (tokenizer : Tokenizer)
    (documents : Array String) : IO Observation := do
  return observeDocs (← runProcessDocs config tokenizer documents)

/-- Time a pure complete-output observation against an already prepared expectation. -/
private def benchPure (repetitions : Nat) (expected : Observation)
    (run : Unit → Observation) : IO Timing := do
  let start ← IO.monoNanosNow
  let mut aggregate := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    let current ← IO.lazyPure run
    if current != expected then
      throw <| IO.userError "pure tokenizer benchmark observation changed"
    aggregate := mix aggregate current.checksum
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Time a checked complete-output observation against an already prepared expectation. -/
private def benchEffect (repetitions : Nat) (expected : Observation)
    (run : Unit → IO Observation) : IO Timing := do
  let start ← IO.monoNanosNow
  let mut aggregate := mix 0 (UInt64.ofNat repetitions)
  for _ in [0:repetitions] do
    let current ← run ()
    if current != expected then
      throw <| IO.userError "effectful tokenizer benchmark observation changed"
    aggregate := mix aggregate current.checksum
  let stop ← IO.monoNanosNow
  return ⟨(stop - start) / repetitions, aggregate⟩

/-- Report one complete-output lane in bytes and tokens per second. -/
private def report (name : String) (bytes tokens : Nat) (timing : Timing) : IO Unit := do
  let seconds := Float.ofNat (max timing.nanos 1) / 1000000000.0
  let mib := Float.ofNat bytes / (1024.0 * 1024.0)
  let mibPerSecond := mib / seconds
  let tokensPerSecond := Float.ofNat tokens / seconds
  IO.println <| s!"{name}\t{mibPerSecond} MiB/s\t{tokensPerSecond} tok/s\t" ++
    s!"{timing.nanos / 1000} us\tchk={timing.aggregate}"

/-- Prepare exact parity, then time every pure and checked path for one corpus. -/
private def benchLane (tokenizer : Tokenizer) (serialConfig parallelConfig : Nlp.Config)
    (workers : Nat) (lane : Lane) : IO Unit := do
  let documents := lane.documents
  let bytes := corpusBytes documents
  let pureTokens ← IO.lazyPure fun _ ↦ observePureTokens tokenizer documents
  let pureTokenDocs ← IO.lazyPure fun _ ↦ observePureTokenDocs tokenizer documents
  let pureProcessed ← IO.lazyPure fun _ ↦ observePureProcess tokenizer documents

  unless pureTokens.tokens == pureTokenDocs.tokens &&
      pureTokens.tokens == pureProcessed.tokens do
    throw <| IO.userError s!"{lane.name}: pure projection token counts differ"

  let serialTokenDocs ← runTokenDocs serialConfig tokenizer documents
  let parallelTokenDocs ← runTokenDocs parallelConfig tokenizer documents
  unless tokenDocParity tokenizer documents serialTokenDocs do
    throw <| IO.userError s!"{lane.name}: checked serial token documents differ from pure"
  unless tokenDocParity tokenizer documents parallelTokenDocs do
    throw <| IO.userError s!"{lane.name}: checked parallel token documents differ from pure"
  let serialTokens := observeDocs serialTokenDocs
  let parallelTokens := observeDocs parallelTokenDocs
  unless serialTokens == pureTokenDocs && parallelTokens == pureTokenDocs do
    throw <| IO.userError s!"{lane.name}: checked token observations differ from pure"

  let serialProcessDocs ← runProcessDocs serialConfig tokenizer documents
  let parallelProcessDocs ← runProcessDocs parallelConfig tokenizer documents
  unless processDocParity tokenizer documents serialProcessDocs do
    throw <| IO.userError s!"{lane.name}: checked serial sentence documents differ from pure"
  unless processDocParity tokenizer documents parallelProcessDocs do
    throw <| IO.userError s!"{lane.name}: checked parallel sentence documents differ from pure"
  let serialProcessed := observeDocs serialProcessDocs
  let parallelProcessed := observeDocs parallelProcessDocs
  unless serialProcessed == pureProcessed && parallelProcessed == pureProcessed do
    throw <| IO.userError s!"{lane.name}: checked sentence observations differ from pure"

  IO.println <| s!"--- {lane.name}: documents={documents.size}; bytes={bytes}; " ++
    s!"tokens={pureTokens.tokens}; sentences={pureProcessed.sentences} ---"

  let pureTiming ← benchPure lane.pureRepetitions pureTokens fun _ ↦
    observePureTokens tokenizer documents
  report "pure scanner" bytes pureTokens.tokens pureTiming

  let serialTiming ← benchEffect lane.effectRepetitions pureTokenDocs fun _ ↦
    observeEffectTokens serialConfig tokenizer documents
  report "checked effect x1" bytes pureTokenDocs.tokens serialTiming

  let parallelTiming ← benchEffect lane.effectRepetitions pureTokenDocs fun _ ↦
    observeEffectTokens parallelConfig tokenizer documents
  report s!"checked weighted x{workers}" bytes pureTokenDocs.tokens parallelTiming
  IO.println s!"parallel/serial speedup={
    Float.ofNat serialTiming.nanos / Float.ofNat (max parallelTiming.nanos 1)}x"

  let pureProcessTiming ← benchPure lane.processRepetitions pureProcessed fun _ ↦
    observePureProcess tokenizer documents
  report "pure tokenize+split" bytes pureProcessed.tokens pureProcessTiming

  let serialProcessTiming ← benchEffect lane.processRepetitions pureProcessed fun _ ↦
    observeEffectProcess serialConfig tokenizer documents
  report "checked process x1" bytes pureProcessed.tokens serialProcessTiming

  let parallelProcessTiming ← benchEffect lane.processRepetitions pureProcessed fun _ ↦
    observeEffectProcess parallelConfig tokenizer documents
  report s!"checked process x{workers}" bytes pureProcessed.tokens parallelProcessTiming
  IO.println s!"process speedup={
    Float.ofNat serialProcessTiming.nanos / Float.ofNat (max parallelProcessTiming.nanos 1)}x"

/-- Run baseline, web-heavy, and adversarial complete-output throughput lanes. -/
def main : IO Unit := do
  let tokenizer := Tokenizer.default
  let hardware := max (System.Platform.Internal.getHardwareConcurrency ()).toNat 1
  let workers := min hardware 8
  let serialConfig : Nlp.Config := {
    numThreads := 1
    parallelMinWeight := 65536
  }
  let parallelConfig : Nlp.Config := {
    numThreads := workers
    parallelMinWeight := 65536
    maxDedicatedThreads := workers
  }
  IO.println s!"hardware threads={hardware}; workers={workers}"
  for lane in lanes do
    benchLane tokenizer serialConfig parallelConfig workers lane

end TokenizeBenchmark

def main : IO Unit := TokenizeBenchmark.main
