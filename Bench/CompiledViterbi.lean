import Nlp.Parse.CompiledViterbi

/-!
# Adaptive compiled Viterbi benchmark

This standalone benchmark compares the legacy indexed kernel with compiled dense and sparse
pair layouts on deterministic binary-heavy and lexical-heavy fixtures. Every timed parse consumes
the complete score and backpointer arrays through a fixed-width checksum. Fixture construction,
index compilation, and one warm-up per lane occur outside the timed region; no machine-specific
performance threshold is asserted.

The final lane compiles a million-nonterminal grammar with one observed binary pair. It reports
the compact sparse index footprint and never constructs the legacy `nNT²` pair table or a chart.
-/

namespace CompiledViterbiBenchmark

open Nlp Nlp.Parse

/-- One stable checksum and the average wall time of a benchmark lane. -/
private structure KernelResult where
  checksum : UInt64
  nanos : Nat

/-- Observable storage metrics for one compiled grammar. -/
private structure Footprint where
  layout : PairLayout
  observedPairs : Nat
  pairOffsets : Nat
  binaryRules : Nat
  lexicalRules : Nat
  checksum : UInt64
deriving Repr, DecidableEq

/-- Mix one word into a deterministic fixed-width checksum. -/
@[inline] private def mix (state value : UInt64) : UInt64 :=
  let shifted := value + (0x9E3779B97F4A7C15 : UInt64) +
    (state <<< 6) + (state >>> 2)
  (state ^^^ shifted) * (0xD6E8FEB86659FD93 : UInt64)

/-- Force every score bit and every exact-source backpointer into one checksum. -/
@[noinline] private def chartChecksum (chart : Viterbi.VitChart) : UInt64 := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat chart.score.size)
  for score in chart.score do
    checksum := mix checksum score.toFloat.toBits
  checksum := mix checksum (UInt64.ofNat chart.back.size)
  for back in chart.back do
    checksum := mix checksum back.rule.toUInt64
    checksum := mix checksum back.split.toUInt64
  return checksum

/-- Run and fully consume the legacy indexed Viterbi kernel. -/
@[noinline] private def legacyChecksum (indexed : IndexedCNF Vit)
    (words : Array Tok) : UInt64 :=
  chartChecksum (Viterbi.ckyVit indexed words)

/-- Run and fully consume the adaptive compiled Viterbi kernel. -/
@[noinline] private def compiledChecksum (compiled : CompiledCNF Vit)
    (words : Array Tok) : UInt64 :=
  chartChecksum (Viterbi.ckyVitCompiled compiled words)

/-- Deterministic canonical Viterbi weight in `[0.55, 0.90]`. -/
@[inline] private def weight (seed : Nat) : Vit :=
  ⟨0.55 + Float.ofNat (seed % 8) / 20.0⟩

private def representativeNT : Nat := 32
private def representativeTokens : Nat := 32
private def representativeLexicalCats : Nat := 8

/-- Binary-heavy fixture with one production for every right-hand-side pair. -/
private def representativeGrammar : CNF Vit :=
  let binary := Array.ofFn (n := representativeNT * representativeNT) fun index ↦
    let left := index.val / representativeNT
    let right := index.val % representativeNT
    let lhs := (left * 13 + right * 7 + 1) % representativeNT
    ⟨UInt32.ofNat lhs, UInt32.ofNat left, UInt32.ofNat right, weight index.val⟩
  let lexical := Array.ofFn
      (n := representativeTokens * representativeLexicalCats) fun index ↦
    let token := index.val / representativeLexicalCats
    let lhs := index.val % representativeLexicalCats
    ⟨UInt32.ofNat lhs, UInt32.ofNat token, weight (index.val * 5 + 3)⟩
  { bin := binary, lex := lexical, start := 0, nNT := representativeNT }

/-- Fixed mixed-token sentence for the binary-heavy fixture. -/
private def representativeWords : Array Tok :=
  Array.ofFn (n := 18) fun index ↦
    UInt32.ofNat ((index.val * 7 + index.val * index.val + 3) % representativeTokens)

private def lexicalNT : Nat := 64
private def lexicalTokens : Nat := 512
private def lexicalCats : Nat := 32

/-- Lexical-heavy fixture with many irrelevant token buckets and no binary productions. -/
private def lexicalGrammar : CNF Vit :=
  let lexical := Array.ofFn (n := lexicalTokens * lexicalCats) fun index ↦
    let token := index.val / lexicalCats
    let lhs := index.val % lexicalCats
    ⟨UInt32.ofNat lhs, UInt32.ofNat token, weight (index.val * 11 + 1)⟩
  { bin := #[], lex := lexical, start := 0, nNT := lexicalNT }

/-- Fixed sentence whose tokens occupy only one quarter of the lexical buckets. -/
private def lexicalWords : Array Tok :=
  Array.ofFn (n := 96) fun index ↦ UInt32.ofNat ((index.val * 37 + 5) % 128)

/-- Compile one benchmark grammar or raise a readable fixture error. -/
private def requireCompiled (name : String) (config : CompileConfig)
    (grammar : CNF Vit) : IO (CompiledCNF Vit) :=
  match CompiledCNF.compileWith config grammar with
  | .ok compiled => pure compiled
  | .error error => throw <| IO.userError s!"{name} compile failed: {repr error}"

/-- Warm up, time repeated runs, and reject checksum instability. -/
private def benchKernel (name : String) (repetitions : Nat)
    (tokens entries : Nat) (run : Unit → UInt64) : IO KernelResult := do
  let expected ← IO.lazyPure fun _ ↦ run ()
  let start ← IO.monoNanosNow
  let mut aggregate := expected
  for _ in [0:repetitions] do
    let current ← IO.lazyPure fun _ ↦ run ()
    if current != expected then
      throw <| IO.userError s!"{name} checksum changed"
    aggregate := mix aggregate current
  let stop ← IO.monoNanosNow
  let nanos := (stop - start) / repetitions
  let seconds := Float.ofNat (max nanos 1) / 1000000000.0
  let tokenRate := Float.ofNat tokens / seconds
  IO.println <| s!"{name}: tokens={tokens} entries={entries} " ++
    s!"elapsed={nanos / 1000} us tokens/s={tokenRate} chk={aggregate}"
  return ⟨expected, nanos⟩

/-- Benchmark legacy, compiled-dense, and compiled-sparse kernels over one fixture. -/
private def benchFixture (name : String) (repetitions : Nat)
    (grammar : CNF Vit) (words : Array Tok) : IO Unit := do
  let pairCells := grammar.nNT * grammar.nNT
  let denseConfig : CompileConfig := { densePairCells := pairCells }
  let sparseConfig : CompileConfig := { densePairCells := pairCells - 1 }
  let indexed := grammar.index
  let dense ← requireCompiled s!"{name} dense" denseConfig grammar
  let sparse ← requireCompiled s!"{name} sparse" sparseConfig grammar
  if dense.pairLayout != .dense || sparse.pairLayout != .sparse then
    throw <| IO.userError s!"{name} adaptive layout selection changed"
  let entries := Chart.entryCount words.size grammar.nNT
  IO.println <| s!"--- {name}: nNT={grammar.nNT} bin={grammar.bin.size} " ++
    s!"lex={grammar.lex.size} pairCells={pairCells} ---"
  let legacy ← benchKernel "legacy indexed" repetitions words.size entries fun _ ↦
    legacyChecksum indexed words
  let compiledDense ←
    benchKernel "compiled dense" repetitions words.size entries fun _ ↦
      compiledChecksum dense words
  let compiledSparse ←
    benchKernel "compiled sparse" repetitions words.size entries fun _ ↦
      compiledChecksum sparse words
  unless legacy.checksum == compiledDense.checksum &&
      legacy.checksum == compiledSparse.checksum do
    throw <| IO.userError s!"{name} kernels disagree"
  IO.println <|
    s!"dense/legacy={Float.ofNat legacy.nanos / Float.ofNat compiledDense.nanos}x " ++
      s!"sparse/legacy={Float.ofNat legacy.nanos / Float.ofNat compiledSparse.nanos}x"

/-- Million-nonterminal grammar used only to exercise compact compilation. -/
private def largeSparseGrammar : CNF Vit :=
  { bin := #[⟨0, 1, 2, ⟨0.75⟩⟩]
    lex := #[⟨1, 70, ⟨0.8⟩⟩, ⟨2, 71, ⟨0.9⟩⟩]
    start := 0
    nNT := 1_000_000 }

/-- Force every compact compiled array while recording its observable footprint. -/
@[noinline] private def compiledFootprint (compiled : CompiledCNF Vit) : Footprint := Id.run do
  let mut checksum := mix 0 (UInt64.ofNat compiled.grammar.nNT)
  for rule in compiled.binaryRules do
    checksum := mix checksum (UInt64.ofNat rule.lhs.toNat)
    checksum := mix checksum (UInt64.ofNat rule.r1.toNat)
    checksum := mix checksum (UInt64.ofNat rule.r2.toNat)
    checksum := mix checksum rule.w.toFloat.toBits
  for source in compiled.binarySources do
    checksum := mix checksum (UInt64.ofNat source)
  let mut layout := PairLayout.dense
  let mut observedPairs := compiled.grammar.nNT * compiled.grammar.nNT
  let mut pairOffsets := 0
  match compiled.binaryIndex with
  | .dense starts =>
    pairOffsets := starts.size
    for offset in starts do
      checksum := mix checksum (UInt64.ofNat offset)
  | .sparse _ keys starts =>
    layout := .sparse
    observedPairs := keys.size
    pairOffsets := starts.size
    for key in keys do
      checksum := mix checksum (UInt64.ofNat key)
    for offset in starts do
      checksum := mix checksum (UInt64.ofNat offset)
  for rule in compiled.lexicalRules do
    checksum := mix checksum (UInt64.ofNat rule.lhs.toNat)
    checksum := mix checksum (UInt64.ofNat rule.tok.toNat)
    checksum := mix checksum rule.w.toFloat.toBits
  for source in compiled.lexicalSources do
    checksum := mix checksum (UInt64.ofNat source)
  for key in compiled.lexicalKeys do
    checksum := mix checksum key.toUInt64
  for offset in compiled.lexicalStarts do
    checksum := mix checksum (UInt64.ofNat offset)
  return ⟨layout, observedPairs, pairOffsets, compiled.binaryRules.size,
    compiled.lexicalRules.size, checksum⟩

/-- Compile and consume the compact large-NT representation once. -/
@[noinline] private def compileFootprint : Except CompileError Footprint :=
  largeSparseGrammar.compile.map compiledFootprint

/-- Warm up and time large-NT sparse compilation without constructing an indexed legacy view. -/
private def benchLargeCompile (repetitions : Nat) : IO Unit := do
  let warm ← IO.lazyPure fun _ ↦ compileFootprint
  let expected ←
    match warm with
    | .ok footprint => pure footprint
    | .error error => throw <| IO.userError s!"large sparse compile failed: {repr error}"
  unless expected.layout == .sparse && expected.observedPairs == 1 &&
      expected.pairOffsets == 2 do
    throw <| IO.userError s!"large sparse footprint is not compact: {repr expected}"
  let start ← IO.monoNanosNow
  let mut aggregate := expected.checksum
  for _ in [0:repetitions] do
    let current ← IO.lazyPure fun _ ↦ compileFootprint
    match current with
    | .error error => throw <| IO.userError s!"large sparse compile failed: {repr error}"
    | .ok footprint =>
      if footprint != expected then
        throw <| IO.userError "large sparse footprint changed"
      aggregate := mix aggregate footprint.checksum
  let stop ← IO.monoNanosNow
  let nanos := (stop - start) / repetitions
  let virtualPairs := largeSparseGrammar.nNT * largeSparseGrammar.nNT
  IO.println <| s!"--- large-nNT compile only: nNT={largeSparseGrammar.nNT} " ++
    s!"virtualPairs={virtualPairs} observedPairs={expected.observedPairs} " ++
    s!"pairOffsets={expected.pairOffsets} bin={expected.binaryRules} " ++
    s!"lex={expected.lexicalRules} elapsed={nanos / 1000} us chk={aggregate} ---"

/-- Run deterministic parser and compact-compilation benchmark lanes. -/
def main : IO Unit := do
  benchFixture "representative binary-heavy" 3 representativeGrammar representativeWords
  benchFixture "lexical-heavy" 3 lexicalGrammar lexicalWords
  benchLargeCompile 5

end CompiledViterbiBenchmark

def main : IO Unit := CompiledViterbiBenchmark.main
