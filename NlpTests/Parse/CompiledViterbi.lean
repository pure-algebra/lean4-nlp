import Nlp.Parse.CompiledViterbi

/-!
# Exact tests for adaptive compiled Viterbi CKY

Compiled execution is compared bit-for-bit and provenance-for-provenance with the legacy indexed
kernel. Dense, sparse, tied, and duplicate-production cases ensure that adaptive storage never
changes source ordinals. A large-nonterminal compile test inspects the compact sparse index without
running the necessarily dense `O(n²·nNT)` chart.
-/

namespace NlpTests.Parse.CompiledViterbi

open Nlp Nlp.Parse

private def scoreBits (chart : Viterbi.VitChart) : Array UInt64 :=
  chart.score.map fun score ↦ score.toFloat.toBits

private def treeSignature (tree : Option Tree) : Option (Array Word × Array (Cat × Nat × Nat)) :=
  tree.map fun parsed ↦ (parsed.yieldWords, parsed.spans)

private def equivalentWith (config : CompileConfig) (grammar : CNF Vit)
    (words : Array Tok) : Bool :=
  match CompiledCNF.compileWith config grammar with
  | .error _ => false
  | .ok compiled =>
    let indexed := grammar.index
    let legacy := Viterbi.ckyVit indexed words
    let adaptive := Viterbi.ckyVitCompiled compiled words
    scoreBits adaptive == scoreBits legacy && adaptive.back == legacy.back &&
      Viterbi.extractCompiledDerivation compiled words adaptive ==
        Viterbi.extractDerivation indexed words legacy &&
      treeSignature (Viterbi.extractCompiledTree compiled words adaptive) ==
        treeSignature (Viterbi.extractTree indexed words legacy)

private def rangeEquivalentWith (config : CompileConfig) (grammar : CNF Vit)
    (words : Array Tok) (start stop : Nat) (expected : Array Tok) : Bool :=
  match CompiledCNF.compileWith config grammar with
  | .error _ => false
  | .ok compiled =>
    let rangeChart := Viterbi.ckyVitCompiledRange compiled words start stop
    let expectedChart := Viterbi.ckyVitCompiled compiled expected
    scoreBits rangeChart == scoreBits expectedChart &&
      rangeChart.back == expectedChart.back &&
      Viterbi.extractCompiledDerivationRange compiled words start stop rangeChart ==
        Viterbi.extractCompiledDerivation compiled expected expectedChart &&
      treeSignature
          (Viterbi.extractCompiledTreeRange compiled words start stop rangeChart) ==
        treeSignature (Viterbi.extractCompiledTree compiled expected expectedChart)

private def emptyRangeEquivalentWith (config : CompileConfig) (grammar : CNF Vit) : Bool :=
  match CompiledCNF.compileWith config grammar with
  | .error _ => false
  | .ok compiled =>
    let words : Array Tok := #[99, 0, 1, 2, 3, 4, 98]
    let rangeChart := Viterbi.ckyVitCompiledRange compiled words 6 1
    let emptyChart := Viterbi.ckyVitCompiled compiled #[]
    scoreBits rangeChart == scoreBits emptyChart && rangeChart.back == emptyChart.back &&
      (Viterbi.extractCompiledDerivationRange compiled words 6 1 rangeChart).isNone

private def compiledDerivationWith? (config : CompileConfig) (grammar : CNF Vit)
    (words : Array Tok) :
    Option Viterbi.Derivation :=
  match CompiledCNF.compileWith config grammar with
  | .error _ => none
  | .ok compiled =>
    Viterbi.extractCompiledDerivation compiled words
      (Viterbi.ckyVitCompiled compiled words)

private def compiledDerivation? (grammar : CNF Vit) (words : Array Tok) :
    Option Viterbi.Derivation :=
  compiledDerivationWith? CompileConfig.default grammar words

private def sentence : Array Tok := #[0, 1, 2, 3, 4]

private def representative : CNF Vit :=
  { bin :=
      #[⟨0, 1, 2, ⟨1.0⟩⟩, ⟨2, 4, 1, ⟨0.7⟩⟩, ⟨2, 2, 3, ⟨0.3⟩⟩,
        ⟨1, 1, 3, ⟨0.4⟩⟩, ⟨3, 5, 1, ⟨1.0⟩⟩]
    lex :=
      #[⟨1, 0, ⟨1.0⟩⟩, ⟨4, 1, ⟨1.0⟩⟩, ⟨1, 2, ⟨0.3⟩⟩,
        ⟨5, 3, ⟨1.0⟩⟩, ⟨1, 4, ⟨0.3⟩⟩]
    start := 0
    nNT := 6 }

/-- The representative parse is bit-identical and keeps its complete derivation provenance. -/
example : equivalentWith CompileConfig.default representative sentence = true := by
  native_decide

private def denseThreshold : CompileConfig := { densePairCells := 36 }

private def sparseThreshold : CompileConfig := { densePairCells := 35 }

private def alwaysSparse : CompileConfig := { densePairCells := 0 }

private def thresholdLayoutsPreserveExactRuns : Bool :=
  match CompiledCNF.compileWith denseThreshold representative,
      CompiledCNF.compileWith sparseThreshold representative with
  | .ok dense, .ok sparse =>
    dense.pairLayout == .dense && sparse.pairLayout == .sparse &&
      equivalentWith denseThreshold representative sentence &&
      equivalentWith sparseThreshold representative sentence
  | _, _ => false

/-- Crossing the exact `6²` threshold changes only layout, never score bits or backpointers. -/
example : thresholdLayoutsPreserveExactRuns = true := by
  native_decide

private def normalizedRangesPreserveExactRuns : Bool :=
  let padded : Array Tok := #[99, 0, 1, 2, 3, 4, 98]
  let clipped : Array Tok := #[99, 0, 1, 2, 3, 4]
  rangeEquivalentWith denseThreshold representative sentence 0 sentence.size sentence &&
    rangeEquivalentWith alwaysSparse representative sentence 0 sentence.size sentence &&
    rangeEquivalentWith denseThreshold representative padded 1 6 sentence &&
    rangeEquivalentWith alwaysSparse representative padded 1 6 sentence &&
    rangeEquivalentWith denseThreshold representative clipped 1 100 sentence &&
    rangeEquivalentWith alwaysSparse representative clipped 1 100 sentence &&
    emptyRangeEquivalentWith denseThreshold representative &&
    emptyRangeEquivalentWith alwaysSparse representative

/-- Dense and sparse ranges preserve exact charts, local derivations, and clamped bounds. -/
example : normalizedRangesPreserveExactRuns = true := by
  native_decide

private def ruleTieGrammar : CNF Vit :=
  { bin := #[⟨0, 3, 4, ⟨1.0⟩⟩, ⟨0, 1, 2, ⟨1.0⟩⟩]
    lex := #[⟨1, 10, ⟨1.0⟩⟩, ⟨3, 10, ⟨1.0⟩⟩,
      ⟨2, 11, ⟨1.0⟩⟩, ⟨4, 11, ⟨1.0⟩⟩]
    start := 0
    nNT := 5 }

private def ruleTieExpected : Viterbi.Derivation :=
  .binary 0 0 1 (.lexical 1 3 10) (.lexical 3 4 11)

/-- Equal scores choose the lowest source-rule ordinal despite compiled bucket order. -/
example :
    (equivalentWith CompileConfig.default ruleTieGrammar #[10, 11] &&
      equivalentWith alwaysSparse ruleTieGrammar #[10, 11] &&
      compiledDerivationWith? alwaysSparse ruleTieGrammar #[10, 11] ==
        some ruleTieExpected &&
      compiledDerivation? ruleTieGrammar #[10, 11] == some ruleTieExpected) = true := by
  native_decide

private def splitTieGrammar : CNF Vit :=
  { bin :=
      #[⟨0, 1, 4, ⟨1.0⟩⟩, ⟨0, 5, 3, ⟨1.0⟩⟩,
        ⟨4, 2, 3, ⟨1.0⟩⟩, ⟨5, 1, 2, ⟨1.0⟩⟩]
    lex := #[⟨1, 20, ⟨1.0⟩⟩, ⟨2, 21, ⟨1.0⟩⟩, ⟨3, 22, ⟨1.0⟩⟩]
    start := 0
    nNT := 6 }

private def splitTieExpected : Viterbi.Derivation :=
  .binary 0 0 1 (.lexical 0 1 20)
    (.binary 2 4 2 (.lexical 1 2 21) (.lexical 2 3 22))

/-- Equal parses at different fenceposts keep the legacy leftmost-split policy exactly. -/
example :
    (equivalentWith CompileConfig.default splitTieGrammar #[20, 21, 22] &&
      equivalentWith alwaysSparse splitTieGrammar #[20, 21, 22] &&
      compiledDerivationWith? alwaysSparse splitTieGrammar #[20, 21, 22] ==
        some splitTieExpected &&
      compiledDerivation? splitTieGrammar #[20, 21, 22] == some splitTieExpected) = true := by
  native_decide

private def duplicateGrammar : CNF Vit :=
  { bin := #[⟨0, 1, 2, ⟨0.4⟩⟩, ⟨0, 1, 2, ⟨0.8⟩⟩]
    lex := #[⟨1, 50, ⟨0.5⟩⟩, ⟨1, 50, ⟨0.9⟩⟩, ⟨2, 51, ⟨1.0⟩⟩]
    start := 0
    nNT := 3 }

private def duplicateExpected : Viterbi.Derivation :=
  .binary 1 0 1 (.lexical 1 1 50) (.lexical 2 2 51)

/-- Duplicate displayed productions retain the exact higher-scoring source positions. -/
example :
    (equivalentWith CompileConfig.default duplicateGrammar #[50, 51] &&
      equivalentWith alwaysSparse duplicateGrammar #[50, 51] &&
      compiledDerivationWith? alwaysSparse duplicateGrammar #[50, 51] ==
        some duplicateExpected &&
      compiledDerivation? duplicateGrammar #[50, 51] == some duplicateExpected) = true := by
  native_decide

private def sparseGrammar : CNF Vit :=
  { bin := #[⟨0, 1, 2, ⟨0.75⟩⟩, ⟨3, 4, 5, ⟨0.2⟩⟩]
    lex := #[⟨1, 60, ⟨0.8⟩⟩, ⟨2, 61, ⟨0.9⟩⟩]
    start := 0
    nNT := 128 }

private def sparseParityAndLayout : Bool :=
  match CompiledCNF.compileWith alwaysSparse sparseGrammar with
  | .error _ => false
  | .ok compiled =>
    equivalentWith alwaysSparse sparseGrammar #[60, 61] &&
      compiled.pairLayout == .sparse &&
      Viterbi.extractCompiledDerivation compiled #[60, 61]
          (Viterbi.ckyVitCompiled compiled #[60, 61]) ==
        some (.binary 0 0 1 (.lexical 0 1 60) (.lexical 1 2 61)) &&
      match compiled.binaryIndex with
      | .dense _ => false
      | .sparse _ keys starts => keys.size == 2 && starts == #[0, 1, 2]

/-- The compact sparse dispatch is bit- and provenance-identical to legacy indexed Viterbi. -/
example : sparseParityAndLayout = true := by
  native_decide

private def zeroUnderflowGrammar : CNF Vit :=
  let tiny : Vit := ⟨Float.ofBits 1⟩
  { bin := #[⟨0, 1, 2, tiny⟩]
    lex := #[⟨1, 80, tiny⟩, ⟨2, 81, ⟨1.0⟩⟩, ⟨0, 82, ⟨0.0⟩⟩]
    start := 0
    nNT := 3 }

private def zeroAndUnderflowStayRejected : Bool :=
  equivalentWith CompileConfig.default zeroUnderflowGrammar #[80, 81] &&
    equivalentWith alwaysSparse zeroUnderflowGrammar #[80, 81] &&
    equivalentWith CompileConfig.default zeroUnderflowGrammar #[82] &&
    equivalentWith alwaysSparse zeroUnderflowGrammar #[82] &&
    (compiledDerivation? zeroUnderflowGrammar #[80, 81]).isNone &&
    (compiledDerivation? zeroUnderflowGrammar #[82]).isNone

/-- Explicit zero and positive products that underflow to zero retain empty provenance exactly. -/
example : zeroAndUnderflowStayRejected = true := by
  native_decide

private def emptyAndUnknownInputsMatch : Bool :=
  equivalentWith CompileConfig.default representative #[] &&
    equivalentWith alwaysSparse representative #[] &&
    equivalentWith CompileConfig.default representative #[99] &&
    equivalentWith alwaysSparse representative #[99] &&
    (compiledDerivation? representative #[]).isNone &&
    (compiledDerivation? representative #[99]).isNone

/-- Empty and unknown-token inputs agree on zero charts, default backs, and failed extraction. -/
example : emptyAndUnknownInputsMatch = true := by
  native_decide

private def largeSparseGrammar : CNF Vit :=
  { bin := #[⟨0, 1, 2, ⟨0.75⟩⟩]
    lex := #[⟨1, 70, ⟨0.8⟩⟩, ⟨2, 71, ⟨0.9⟩⟩]
    start := 0
    nNT := 1_000_000 }

private def largeSparseIndexIsLinearInObservedRules : Bool :=
  match largeSparseGrammar.compile with
  | .error _ => false
  | .ok compiled =>
    compiled.pairLayout == .sparse && compiled.binaryRules.size == 1 &&
      compiled.binarySources == #[0] &&
      match compiled.binaryIndex with
      | .dense _ => false
      | .sparse _ keys starts => keys.size == 1 && starts == #[0, 1]

/-- One observed pair at one million NTs compiles to two offsets, never an `nNT²` array. -/
example : largeSparseIndexIsLinearInObservedRules = true := by
  native_decide

end NlpTests.Parse.CompiledViterbi
