import Nlp

/-!
# English morphology throughput benchmark

This executable measures the pure column kernel and the checked, token-weighted effectful corpus
API.  It validates checksum equality but deliberately sets no machine-specific speed threshold.
-/

namespace MorphologyBenchmark

open Nlp

private def lexemes : Array Morphology.Lexeme :=
  #[⟨.noun, "dog"⟩, ⟨.verb, "run"⟩, ⟨.verb, "go"⟩, ⟨.auxiliary, "can"⟩,
    ⟨.particle, "not"⟩]

private def exceptions : Array Morphology.ExceptionEntry :=
  #[⟨.verb, "running", "run"⟩, ⟨.auxiliary, "ca", "can"⟩,
    ⟨.particle, "n't", "not"⟩]

private def model : Morphology.Model :=
  match Morphology.Model.compile lexemes exceptions with
  | .ok value => value
  | .error _ => Morphology.Model.empty

private def item (index : Nat) : String × String :=
  match index % 5 with
  | 0 => ("dogs", "NOUN")
  | 1 => ("running", "VERB")
  | 2 => ("ca", "AUX")
  | 3 => ("n't", "PART")
  | _ => ("go", "VERB")

private def document (count : Nat) : Doc [.pos, .tokens] := Id.run do
  let mut text := ""
  let mut spans := Array.emptyWithCapacity count
  let mut forms := Array.emptyWithCapacity count
  let mut tags := Array.emptyWithCapacity count
  for index in [0:count] do
    let (form, tag) := item index
    let start := text.utf8ByteSize
    text := text ++ form
    let stop := text.utf8ByteSize
    spans := spans.push ⟨start, stop⟩
    forms := forms.push form
    tags := tags.push tag
    if index + 1 < count then
      text := text ++ " "
  return { text, spans, forms, pos := tags }

private def corpus : Array (Doc [.pos, .tokens]) :=
  Array.replicate 2048 (document 256)

@[noinline] private def pureChecksum (morphology : Morphology.Model)
    (documents : Array (Doc [.pos, .tokens])) : Nat :=
  documents.foldl (fun total doc ↦
    let output := morphology.lemmatizeDoc doc
    output.lemma.foldl (fun sum lemma ↦ sum + lemma.utf8ByteSize) total) 0

private def effectChecksum (config : Config) (morphology : Morphology.Model)
    (documents : Array (Doc [.pos, .tokens])) : IO Nat := do
  match ← NLP.runIO config <| NLP.lemmatizeManyWithMinTokens 16384 morphology documents with
  | .ok output =>
    return output.foldl (fun total doc ↦
      doc.lemma.foldl (fun sum lemma ↦ sum + lemma.utf8ByteSize) total) 0
  | .error cause => throw <| IO.userError s!"morphology benchmark failed: {cause}"

private def benchPure (repetitions : Nat) (morphology : Morphology.Model)
    (documents : Array (Doc [.pos, .tokens])) : IO (Nat × Nat) := do
  let expected ← IO.lazyPure fun _ ↦ pureChecksum morphology documents
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:repetitions] do
    checksum := checksum + (← IO.lazyPure fun _ ↦ pureChecksum morphology documents)
  let stop ← IO.monoNanosNow
  if checksum != expected * repetitions then
    throw <| IO.userError "pure morphology benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

private def benchEffect (repetitions : Nat) (config : Config)
    (morphology : Morphology.Model) (documents : Array (Doc [.pos, .tokens])) :
    IO (Nat × Nat) := do
  let expected ← effectChecksum config morphology documents
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [0:repetitions] do
    checksum := checksum + (← effectChecksum config morphology documents)
  let stop ← IO.monoNanosNow
  if checksum != expected * repetitions then
    throw <| IO.userError "effectful morphology benchmark checksum changed"
  return (expected, (stop - start) / repetitions)

private def report (name : String) (tokens nanos : Nat) : IO Unit := do
  let seconds := Float.ofNat nanos / 1000000000.0
  let throughput := Float.ofNat tokens / seconds
  IO.println s!"{name}\t{throughput} tok/s\t{nanos / 1000} us"

def main : IO Unit := do
  let documents := corpus
  let tokens := documents.foldl (fun total doc ↦ total + doc.size) 0
  let hardware := max (System.Platform.Internal.getHardwareConcurrency ()).toNat 1
  let workers := min hardware 8
  if !documents.all fun doc ↦ decide doc.SemanticWF then
    throw <| IO.userError "morphology benchmark fixture is not semantically valid"
  IO.println s!"documents={documents.size}; tokens={tokens}; hardware threads={hardware}"

  let (pureResult, pureNanos) ← benchPure 5 model documents
  report "pure lemma columns" tokens pureNanos

  let serialConfig : Config := { numThreads := 1, parallelMinWeight := 16384 }
  let (serialResult, serialNanos) ← benchEffect 3 serialConfig model documents
  if serialResult != pureResult then
    throw <| IO.userError "checked serial morphology differs from the pure kernel"
  report "checked effect x1" tokens serialNanos

  let parallelConfig : Config := {
    numThreads := workers
    parallelMinWeight := 16384
    maxDedicatedThreads := workers
  }
  let (parallelResult, parallelNanos) ← benchEffect 3 parallelConfig model documents
  if parallelResult != pureResult then
    throw <| IO.userError "checked parallel morphology differs from the pure kernel"
  report s!"checked weighted x{workers}" tokens parallelNanos
  IO.println s!"parallel/serial speedup={
    Float.ofNat serialNanos / Float.ofNat parallelNanos}x"

end MorphologyBenchmark

def main : IO Unit := MorphologyBenchmark.main
