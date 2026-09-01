import Nlp

/-!
# Tokenization throughput benchmark

This standalone executable reports byte and token throughput for the pure scanner and the checked,
byte-weighted effectful corpus API. It asserts aggregate token-count equality but intentionally
sets no machine-specific performance threshold.
-/

namespace TokenizeBenchmark

open Nlp Nlp.Tokenize

private def repeatText (count : Nat) (text : String) : String :=
  String.join (List.replicate count text)

private def asciiParagraph : String :=
  "The U.S. team can't re-index 1,234.50 school-aged records. Another sentence follows! "

private def unicodeParagraph : String :=
  "Unicode café 猫 😀 and e\u0301 remain source-aligned. ¿Otra oración? 你好世界。 "

private def corpus : Array String :=
  Array.ofFn (n := 2048) fun index ↦
    if index.val % 8 = 0 then repeatText 8 unicodeParagraph
    else if index.val % 3 = 0 then repeatText 4 asciiParagraph
    else asciiParagraph

private def corpusBytes (documents : Array String) : Nat :=
  documents.foldl (fun total text ↦ total + text.utf8ByteSize) 0

@[noinline] private def pureChecksum (tokenizer : Tokenizer)
    (documents : Array String) : Nat :=
  documents.foldl (fun total text ↦ total + (tokenizer.tokenize text).size) 0

private def effectChecksum (config : Nlp.Config) (tokenizer : Tokenizer)
    (documents : Array String) : IO Nat := do
  match ← NLP.runIO config (NLP.tokenizeTextsWithMinBytes 65536 tokenizer documents) with
  | .ok output => return output.foldl (fun total doc ↦ total + doc.size) 0
  | .error cause => throw <| IO.userError s!"tokenizer benchmark failed: {cause}"

@[noinline] private def pureProcessChecksum (tokenizer : Tokenizer)
    (documents : Array String) : Nat × Nat :=
  documents.foldl (fun (tokens, sentences) text ↦
    let document := tokenizer.process text
    (tokens + document.size, sentences + document.sentEnd.size)) (0, 0)

private def effectProcessChecksum (config : Nlp.Config) (tokenizer : Tokenizer)
    (documents : Array String) : IO (Nat × Nat) := do
  match ← NLP.runIO config
      (NLP.processTextsWithMinBytes 65536 tokenizer documents) with
  | .ok output =>
      return output.foldl (fun (tokens, sentences) document ↦
        (tokens + document.size, sentences + document.sentEnd.size)) (0, 0)
  | .error cause => throw <| IO.userError s!"sentence benchmark failed: {cause}"

private def report (name : String) (bytes tokens nanos : Nat) : IO Unit := do
  let seconds := Float.ofNat nanos / 1000000000.0
  let mib := Float.ofNat bytes / (1024.0 * 1024.0)
  let mibPerSecond := mib / seconds
  let tokensPerSecond := Float.ofNat tokens / seconds
  IO.println s!"{name}\t{mibPerSecond} MiB/s\t{tokensPerSecond} tok/s\t{nanos / 1000} us"

private def benchPure (repetitions : Nat) (tokenizer : Tokenizer)
    (documents : Array String) : IO (Nat × Nat) := do
  let expected := pureChecksum tokenizer documents
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:repetitions] do
    checksum := checksum + pureChecksum tokenizer documents
  let stop ← IO.monoNanosNow
  if checksum != expected * repetitions then
    throw <| IO.userError "pure tokenizer benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

private def benchEffect (repetitions : Nat) (config : Nlp.Config) (tokenizer : Tokenizer)
    (documents : Array String) : IO (Nat × Nat) := do
  let expected ← effectChecksum config tokenizer documents
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:repetitions] do
    checksum := checksum + (← effectChecksum config tokenizer documents)
  let stop ← IO.monoNanosNow
  if checksum != expected * repetitions then
    throw <| IO.userError "effectful tokenizer benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

private def benchPureProcess (repetitions : Nat) (tokenizer : Tokenizer)
    (documents : Array String) : IO ((Nat × Nat) × Nat) := do
  let expected := pureProcessChecksum tokenizer documents
  let start ← IO.monoNanosNow
  let mut checksum := (0, 0)
  for _ in [0:repetitions] do
    let current := pureProcessChecksum tokenizer documents
    checksum := (checksum.1 + current.1, checksum.2 + current.2)
  let stop ← IO.monoNanosNow
  if checksum != (expected.1 * repetitions, expected.2 * repetitions) then
    throw <| IO.userError "pure sentence benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

private def benchEffectProcess (repetitions : Nat) (config : Nlp.Config)
    (tokenizer : Tokenizer) (documents : Array String) : IO ((Nat × Nat) × Nat) := do
  let expected ← effectProcessChecksum config tokenizer documents
  let start ← IO.monoNanosNow
  let mut checksum := (0, 0)
  for _ in [0:repetitions] do
    let current ← effectProcessChecksum config tokenizer documents
    checksum := (checksum.1 + current.1, checksum.2 + current.2)
  let stop ← IO.monoNanosNow
  if checksum != (expected.1 * repetitions, expected.2 * repetitions) then
    throw <| IO.userError "effectful sentence benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

def main : IO Unit := do
  let tokenizer := Tokenizer.default
  let documents := corpus
  let bytes := corpusBytes documents
  let hardware := max (System.Platform.Internal.getHardwareConcurrency ()).toNat 1
  let workers := min hardware 8
  IO.println s!"documents={documents.size}; bytes={bytes}; hardware threads={hardware}"

  let (pureTokens, pureNanos) ← benchPure 5 tokenizer documents
  report "pure scanner" bytes pureTokens pureNanos

  let serialConfig : Nlp.Config := {
    numThreads := 1
    parallelMinWeight := 65536
  }
  let (serialTokens, serialNanos) ← benchEffect 3 serialConfig tokenizer documents
  if serialTokens != pureTokens then
    throw <| IO.userError "checked serial token count differs from the pure scanner"
  report "checked effect x1" bytes serialTokens serialNanos

  let parallelConfig : Nlp.Config := {
    numThreads := workers
    parallelMinWeight := 65536
    maxDedicatedThreads := workers
  }
  let (parallelTokens, parallelNanos) ← benchEffect 3 parallelConfig tokenizer documents
  if parallelTokens != pureTokens then
    throw <| IO.userError "checked parallel token count differs from the pure scanner"
  report s!"checked weighted x{workers}" bytes parallelTokens parallelNanos
  IO.println s!"parallel/serial speedup={Float.ofNat serialNanos / Float.ofNat parallelNanos}x"

  let (pureProcessed, pureProcessNanos) ← benchPureProcess 3 tokenizer documents
  report "pure tokenize+split" bytes pureProcessed.1 pureProcessNanos
  IO.println s!"sentences={pureProcessed.2}"

  let (serialProcessed, serialProcessNanos) ←
    benchEffectProcess 2 serialConfig tokenizer documents
  if serialProcessed != pureProcessed then
    throw <| IO.userError "checked serial sentence result differs from the pure pipeline"
  report "checked process x1" bytes serialProcessed.1 serialProcessNanos

  let (parallelProcessed, parallelProcessNanos) ←
    benchEffectProcess 2 parallelConfig tokenizer documents
  if parallelProcessed != pureProcessed then
    throw <| IO.userError "checked parallel sentence result differs from the pure pipeline"
  report s!"checked process x{workers}" bytes parallelProcessed.1 parallelProcessNanos
  IO.println s!"process speedup={
    Float.ofNat serialProcessNanos / Float.ofNat parallelProcessNanos}x"

end TokenizeBenchmark

def main : IO Unit := TokenizeBenchmark.main
