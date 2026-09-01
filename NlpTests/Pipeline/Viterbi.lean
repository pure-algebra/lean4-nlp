import Nlp.Pipeline.Viterbi

namespace NlpTests.Pipeline.Viterbi

open Nlp

private def grammar : CNF Vit :=
  { bin := #[⟨0, 1, 2, ⟨1.0⟩⟩]
    lex := #[⟨1, 10, ⟨1.0⟩⟩, ⟨2, 11, ⟨1.0⟩⟩]
    start := 0
    nNT := 3 }

private def invalidGrammar : CNF Vit :=
  { bin := #[⟨0, 1, 3, ⟨1.0⟩⟩]
    lex := #[⟨1, 10, ⟨1.0⟩⟩]
    start := 0
    nNT := 3 }

private def largeSparseGrammar : CNF Vit :=
  { bin := #[]
    lex := #[⟨0, 10, ⟨1.0⟩⟩]
    start := 0
    nNT := 1_000_000 }

private def withBinaryWeight (value : Float) : CNF Vit :=
  { grammar with bin := #[⟨0, 1, 2, ⟨value⟩⟩] }

private def withLexicalWeight (value : Float) : CNF Vit :=
  { grammar with lex := #[⟨1, 10, ⟨value⟩⟩, ⟨2, 11, ⟨1.0⟩⟩] }

def testPureCompileAndTree : IO Unit := do
  let .ok model := ViterbiModel.compile grammar
    | throw <| IO.userError "valid Viterbi grammar did not compile"
  let result ← NLP.runIO {} <| NLP.parseTree model #[10, 11]
  match result with
  | .ok (.ok tree) =>
      if tree.yieldWords != #[10, 11] then
        throw <| IO.userError "Viterbi tree did not preserve the sentence yield"
  | _ => throw <| IO.userError "valid sentence did not produce a Viterbi tree"

def testCheckedRanges : IO Unit := do
  let .ok model := ViterbiModel.compile grammar
    | throw <| IO.userError "checked-range Viterbi fixture did not compile"
  let words : Array Tok := #[10, 11]
  let padded : Array Tok := #[99, 10, 11, 98]
  match model.derivationRangeChecked? padded 1 3 with
  | .ok (some derivation) =>
      if some derivation != model.derivation? words then
        throw <| IO.userError "checked offset range changed exact local provenance"
      if derivation.toTree.yieldWords != words then
        throw <| IO.userError "checked offset range read outside its source bounds"
  | .ok none => throw <| IO.userError "reachable checked offset range returned no derivation"
  | .error _ => throw <| IO.userError "reachable checked offset range reported extraction failure"
  match model.derivationRangeChecked? padded 0 1 with
  | .ok none => pure ()
  | _ => throw <| IO.userError "unreachable checked range was not ordinary none"
  match (model.derivationRangeChecked? padded 3 1,
      model.derivationRangeChecked? padded 2 2) with
  | (.ok none, .ok none) => pure ()
  | _ => throw <| IO.userError "normalized empty checked ranges were not ordinary none"

def testNoAnalysis : IO Unit := do
  match ← NLP.runIO {} do
    let model ← NLP.compileViterbiModel grammar
    NLP.parseTree model #[10, 99]
  with
  | .ok .noAnalysis => pure ()
  | _ => throw <| IO.userError "rejected sentence was not reported as no analysis"

def testTooLong : IO Unit := do
  match ← NLP.runIO { maxLen := 1 } do
    let model ← NLP.compileViterbiModel grammar
    NLP.parseTree model #[10, 11]
  with
  | .ok (.skipped (.tooLong 2 1)) => pure ()
  | _ => throw <| IO.userError "Viterbi parser did not preserve the length policy as data"

def testChartBudget : IO Unit := do
  match ← NLP.runIO { maxChartEntries := 1 } do
    let model ← NLP.compileViterbiModel grammar
    NLP.parseTree model #[10, 11]
  with
  | .ok (.skipped (.chartTooLarge 9 1)) => pure ()
  | _ => throw <| IO.userError "Viterbi parser entered a chart beyond its allocation budget"

def testLargeSparseChartBudget : IO Unit := do
  match ← NLP.runIO { maxChartEntries := 100 } do
    let model ← NLP.compileViterbiModel largeSparseGrammar
    NLP.parseTree model #[10]
  with
  | .ok (.skipped (.chartTooLarge 1_000_000 100)) => pure ()
  | _ => throw <| IO.userError "large sparse model bypassed the dense-chart allocation policy"

def testInvalidGrammarSource : IO Unit := do
  match ← NLP.runIO {} <| NLP.compileViterbiModel invalidGrammar "models/parser.cnf" with
  | .error (.modelCorrupt source why) =>
      if source != "models/parser.cnf" ||
          why != "binary rule 0 has nonterminals lhs=0, left=1, right=3; " ++
            "every nonterminal must be in [0, 3)" then
        throw <| IO.userError "Viterbi validation lost its model path or rule detail"
  | _ => throw <| IO.userError "invalid Viterbi grammar was not a modelCorrupt failure"

def testOrderedBatch : IO Unit := do
  let sentences : Array (Array Tok) := #[#[10, 11], #[10, 99], #[10, 11, 11], #[10, 11]]
  let config : Config := {
    numThreads := 4
    maxLen := 2
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config do
    let model ← NLP.compileViterbiModel grammar
    NLP.parseTreesWithGrain 2 model sentences
  with
  | .ok #[.ok first, .noAnalysis, .skipped (.tooLong 3 2), .ok last] =>
      if first.yieldWords != #[10, 11] || last.yieldWords != #[10, 11] then
        throw <| IO.userError "ordered Viterbi batch returned incorrect trees"
  | _ => throw <| IO.userError "Viterbi batch did not preserve input order and statuses"

def testInvalidWeights : IO Unit := do
  let nanBits : UInt64 := 0x7ff8000000000001
  let negativeZeroBits : UInt64 := 0x8000000000000000
  match ViterbiModel.compile (withLexicalWeight (Float.ofBits nanBits)) with
  | .error (.invalidLexicalWeight 0 value bits) =>
      if !value.isNaN || bits != value.toBits then
        throw <| IO.userError "NaN validation lost its lexical source or stored float bits"
  | _ => throw <| IO.userError "NaN lexical weight was accepted"
  match ViterbiModel.compile (withBinaryWeight 1.25) with
  | .error (.invalidBinaryWeight 0 value bits) =>
      if bits != (1.25 : Float).toBits || value.toBits != bits then
        throw <| IO.userError "out-of-range validation lost its binary source or value"
  | _ => throw <| IO.userError "out-of-range binary weight was accepted"
  match ViterbiModel.compile (withLexicalWeight (Float.ofBits negativeZeroBits)) with
  | .error (.invalidLexicalWeight 0 value bits) =>
      if bits != negativeZeroBits || value.toBits != negativeZeroBits then
        throw <| IO.userError "negative-zero validation lost its exact float bits"
  | _ => throw <| IO.userError "negative-zero lexical weight was accepted"

def testInvalidWeightSource : IO Unit := do
  let bits : UInt64 := 0x8000000000000000
  let bad := withLexicalWeight (Float.ofBits bits)
  match ← NLP.runIO {} <| NLP.compileViterbiModel bad "models/weighted.cnf" with
  | .error (.modelCorrupt source why) =>
      let expectedPrefix := "lexical rule 0 has invalid Viterbi weight"
      if source != "models/weighted.cnf" || !why.startsWith expectedPrefix then
        throw <| IO.userError "invalid weight lost its path-aware actionable detail"
  | _ => throw <| IO.userError "invalid weight was not mapped to modelCorrupt"

def testCancelled : IO Unit := do
  let .ok model := ViterbiModel.compile grammar
    | throw <| IO.userError "cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.parseTree model #[10, 11])).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "Viterbi parser lost its cancellation reason"

#eval testPureCompileAndTree
#eval testCheckedRanges
#eval testNoAnalysis
#eval testTooLong
#eval testChartBudget
#eval testLargeSparseChartBudget
#eval testInvalidGrammarSource
#eval testOrderedBatch
#eval testInvalidWeights
#eval testInvalidWeightSource
#eval testCancelled

end NlpTests.Pipeline.Viterbi
