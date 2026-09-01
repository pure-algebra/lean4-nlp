import Nlp.Pipeline.Pos

/-!
# Named HMM part-of-speech throughput benchmark

This executable measures the sentence-aware pure document kernel and the checked, token-weighted
effectful corpus API. It validates checksum equality and intentionally sets no machine-specific
throughput threshold.
-/

namespace PosBenchmark

open Nlp Nlp.Sequence

/-- A compact tag inventory large enough to exercise the quadratic HMM transition kernel. -/
private def tags : Array String :=
  #["ADJ", "ADP", "ADV", "AUX", "DET", "NOUN", "PRON", "VERB"]

/-- Synthetic exact-match word names used by both estimation and benchmark documents. -/
private def words : Array String :=
  Array.ofFn (n := 128) fun index ↦ s!"word{index.val}"

/-- Deterministic named training sentences for the benchmark-only model. -/
private def training : Array (Array (String × String)) :=
  Array.ofFn (n := 64) fun sentence ↦
    Array.ofFn (n := 32) fun position ↦
      let word := (sentence.val * 17 + position.val * 7) % words.size
      (words[word]!, tags[word % tags.size]!)

/-- The validated named HMM request resolved once before benchmark timing starts. -/
private def tagger? : Except PosTagger.CompileError PosTagger :=
  PosTagger.estimate training

/-- Build one valid four-sentence token document without timing fixture construction. -/
private def document (seed count : Nat) : Doc [.sents, .tokens] := Id.run do
  let mut text := ""
  let mut spans := Array.emptyWithCapacity count
  let mut forms := Array.emptyWithCapacity count
  let mut sentEnd := Array.emptyWithCapacity ((count + 31) / 32)
  for index in [0:count] do
    let form := words[(seed * 19 + index * 11) % words.size]!
    let start := text.utf8ByteSize
    text := text ++ form
    let stop := text.utf8ByteSize
    spans := spans.push ⟨start, stop⟩
    forms := forms.push form
    if (index + 1) % 32 = 0 then
      sentEnd := sentEnd.push (index + 1)
    if index + 1 < count then
      text := text ++ " "
  if 0 < count && count % 32 != 0 then
    sentEnd := sentEnd.push count
  return { text, spans, forms, sentEnd }

/-- Fixed corpus whose construction and semantic validation are outside timed regions. -/
private def corpus : Array (Doc [.sents, .tokens]) :=
  Array.ofFn (n := 1024) fun index ↦ document index.val 128

/-- Force complete pure POS columns into an observable checksum. -/
@[noinline] private def pureChecksum (model : PosTagger)
    (documents : Array (Doc [.sents, .tokens])) : Nat :=
  documents.foldl (fun total doc ↦
    (model.tagDoc doc).pos.foldl (fun sum tag ↦ sum + tag.utf8ByteSize) total) 0

/-- Run the checked ordered corpus API and force its complete POS columns. -/
private def effectChecksum (config : Config) (model : PosTagger)
    (documents : Array (Doc [.sents, .tokens])) : IO Nat := do
  match ← NLP.runIO config <| NLP.tagManyWithMinTokens 4096 model documents with
  | .ok output =>
    return output.foldl (fun total doc ↦
      doc.pos.foldl (fun sum tag ↦ sum + tag.utf8ByteSize) total) 0
  | .error cause => throw <| IO.userError s!"POS benchmark failed: {cause}"

/-- Measure the average pure-kernel wall time while checking result stability. -/
private def benchPure (repetitions : Nat) (model : PosTagger)
    (documents : Array (Doc [.sents, .tokens])) : IO (Nat × Nat) := do
  let expected ← IO.lazyPure fun _ ↦ pureChecksum model documents
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:repetitions] do
    checksum := checksum + (← IO.lazyPure fun _ ↦ pureChecksum model documents)
  let stop ← IO.monoNanosNow
  if checksum != expected * repetitions then
    throw <| IO.userError "pure POS benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

/-- Measure the average checked effectful wall time while checking result stability. -/
private def benchEffect (repetitions : Nat) (config : Config) (model : PosTagger)
    (documents : Array (Doc [.sents, .tokens])) : IO (Nat × Nat) := do
  let expected ← effectChecksum config model documents
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:repetitions] do
    checksum := checksum + (← effectChecksum config model documents)
  let stop ← IO.monoNanosNow
  if checksum != expected * repetitions then
    throw <| IO.userError "effectful POS benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

/-- Render token throughput for one benchmark lane. -/
private def report (name : String) (tokens nanos : Nat) : IO Unit := do
  let seconds := Float.ofNat nanos / 1000000000.0
  let throughput := Float.ofNat tokens / seconds
  IO.println s!"{name}\t{throughput} tok/s\t{nanos / 1000} us"

/-- Run pure, checked serial, and checked parallel POS throughput lanes. -/
def main : IO Unit := do
  let tagger ←
    match tagger? with
    | .ok value => pure value
    | .error cause => throw <| IO.userError s!"POS benchmark model failed: {repr cause}"
  let documents := corpus
  let tokens := documents.foldl (fun total doc ↦ total + doc.size) 0
  let hardware := max (System.Platform.Internal.getHardwareConcurrency ()).toNat 1
  let workers := min hardware 8
  if !documents.all fun doc ↦ decide doc.SemanticWF then
    throw <| IO.userError "POS benchmark fixture is not semantically valid"
  IO.println <| s!"documents={documents.size}; tokens={tokens}; tags={tagger.tagNames.size}; " ++
    s!"hardware threads={hardware}"

  let (pureResult, pureNanos) ← benchPure 5 tagger documents
  report "pure sentence-aware POS" tokens pureNanos

  let serialConfig : Config := { numThreads := 1, parallelMinWeight := 4096 }
  let (serialResult, serialNanos) ← benchEffect 3 serialConfig tagger documents
  if serialResult != pureResult then
    throw <| IO.userError "checked serial POS differs from the pure kernel"
  report "checked effect x1" tokens serialNanos

  let parallelConfig : Config := {
    numThreads := workers
    parallelMinWeight := 4096
    maxDedicatedThreads := workers
  }
  let (parallelResult, parallelNanos) ← benchEffect 3 parallelConfig tagger documents
  if parallelResult != pureResult then
    throw <| IO.userError "checked parallel POS differs from the pure kernel"
  report s!"checked weighted x{workers}" tokens parallelNanos
  IO.println s!"parallel/serial speedup={
    Float.ofNat serialNanos / Float.ofNat parallelNanos}x"

end PosBenchmark

def main : IO Unit := PosBenchmark.main
