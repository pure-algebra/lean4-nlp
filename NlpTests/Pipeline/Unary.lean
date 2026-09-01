import Nlp.Pipeline.Unary

/-! # Functional and effectful tests for unary-aware Viterbi models -/

namespace NlpTests.Pipeline.Unary

open Nlp Nlp.Grammar

private def interner : Interner :=
  { names := #["S", "VP", "N", "V", "dogs", "run", "cats", "sleep", "X", "x"] }

private def sourceTree : Tree :=
  .node 0 (.node 1 (.node 2 (.leaf 4) #[]) #[.node 3 (.leaf 5) #[]]) #[]

private def sourceGrammar : Except InduceError (TreebankGrammar Vit) :=
  (Grammar.induce interner #[sourceTree]).map fun grammar ↦
    grammar.mapWeights fun _ ↦ (1 : Vit)

private def requireGrammar : IO (TreebankGrammar Vit) :=
  match sourceGrammar with
  | .ok grammar => pure grammar
  | .error error => throw <| IO.userError s!"unary fixture induction failed: {repr error}"

private def treeSignature (tree : Tree) : Array Word × Array (Cat × Nat × Nat) :=
  (tree.yieldWords, tree.spans)

def testPureFunctionalRoundTrip : IO Unit := do
  let grammar ← requireGrammar
  let .ok model := UnaryViterbiModel.compileWith .default { densePairCells := 0 } grammar
    | throw <| IO.userError "valid unary Viterbi model did not compile"
  if model.parser.compiled.pairLayout != .sparse then
    throw <| IO.userError "forced sparse unary model selected dense pair storage"
  if (model.parse? #[4, 5]).map treeSignature != some (treeSignature sourceTree) then
    throw <| IO.userError "pure unary Viterbi parsing did not restore the source tree"

private def checkPureRangeRoundTrip (model : UnaryViterbiModel) : IO Unit := do
  let words : Array Tok := #[4, 5]
  let padded : Array Tok := #[99, 4, 5, 98]
  let clipped : Array Tok := #[99, 4, 5]
  let full := model.derivation? words
  let fullRange := model.derivationRange? words 0 words.size
  let offsetRange := model.derivationRange? padded 1 3
  let clippedRange := model.derivationRange? clipped 1 100
  if fullRange != full || offsetRange != full || clippedRange != full then
    throw <| IO.userError "unary derivation range changed exact local provenance"
  if (model.derivationRange? padded 3 1).isSome then
    throw <| IO.userError "reversed unary range did not normalize to empty input"
  let checkedOffset := model.derivationRangeChecked? padded 1 3
  match checkedOffset, model.parser.derivationRangeChecked? padded 1 3 with
  | .ok unary, .ok delegated =>
      if unary != delegated then
        throw <| IO.userError "unary checked range changed delegated provenance"
  | .error .generatedChartExtraction, .error .generatedChartExtraction => pure ()
  | _, _ => throw <| IO.userError "unary checked range changed the delegated result shape"
  match checkedOffset with
  | .ok (some derivation) =>
      if offsetRange != some derivation then
        throw <| IO.userError "checked unary range changed compatibility provenance"
      if derivation.toTree.yieldWords != words then
        throw <| IO.userError "checked unary range read tokens outside its source bounds"
      match model.restoreDerivation? derivation with
      | none => throw <| IO.userError "checked unary derivation failed source restoration"
      | some restored =>
          if treeSignature restored != treeSignature sourceTree then
            throw <| IO.userError "checked unary derivation restored a different source tree"
  | .ok none => throw <| IO.userError "valid checked unary range had no derivation"
  | .error _ => throw <| IO.userError "valid checked unary range reported extraction failure"
  if (model.parseRange? padded 1 3).map treeSignature != some (treeSignature sourceTree) then
    throw <| IO.userError "unary parse-range convenience wrapper changed the source tree"

def testPureRangeRoundTrip : IO Unit := do
  let grammar ← requireGrammar
  let .ok dense :=
      UnaryViterbiModel.compileWith .default { densePairCells := 1000 } grammar
    | throw <| IO.userError "valid dense unary range model did not compile"
  let .ok sparse :=
      UnaryViterbiModel.compileWith .default { densePairCells := 0 } grammar
    | throw <| IO.userError "valid sparse unary range model did not compile"
  if dense.parser.compiled.pairLayout != .dense ||
      sparse.parser.compiled.pairLayout != .sparse then
    throw <| IO.userError "unary range fixtures did not select both compiled layouts"
  checkPureRangeRoundTrip dense
  checkPureRangeRoundTrip sparse

def testEffectfulRoundTrip : IO Unit := do
  let grammar ← requireGrammar
  match ← NLP.runIO {} do
    let model ← NLP.compileUnaryViterbiModel grammar
    NLP.parseUnaryTree model #[4, 5]
  with
  | .ok (.ok tree) =>
      if treeSignature tree != treeSignature sourceTree then
        throw <| IO.userError "effectful unary Viterbi parsing changed the source tree"
  | _ => throw <| IO.userError "valid unary sentence did not produce a restored tree"

def testNoAnalysisAndLengthPolicy : IO Unit := do
  let grammar ← requireGrammar
  match ← NLP.runIO { maxLen := 1 } do
    let model ← NLP.compileUnaryViterbiModel grammar
    return (← NLP.parseUnaryTree model #[99], ← NLP.parseUnaryTree model #[4, 5])
  with
  | .ok (.noAnalysis, .skipped (.tooLong 2 1)) => pure ()
  | _ => throw <| IO.userError "unary parser lost no-analysis or length-policy data"

def testChartBudget : IO Unit := do
  let grammar ← requireGrammar
  match ← NLP.runIO { maxChartEntries := 1 } do
    let model ← NLP.compileUnaryViterbiModel grammar
    NLP.parseUnaryTree model #[4, 5]
  with
  | .ok (.skipped (.chartTooLarge 12 1)) => pure ()
  | _ => throw <| IO.userError "unary parser entered a chart beyond its allocation budget"

def testOrderedBatch : IO Unit := do
  let grammar ← requireGrammar
  let sentences : Array (Array Tok) := #[#[4, 5], #[4, 99], #[4, 5, 5], #[4, 5]]
  let config : Config := {
    numThreads := 4
    maxLen := 2
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config do
    let model ← NLP.compileUnaryViterbiModel grammar
    NLP.parseUnaryTreesWithGrain 2 model sentences
  with
  | .ok #[.ok first, .noAnalysis, .skipped (.tooLong 3 2), .ok last] =>
      if treeSignature first != treeSignature sourceTree ||
          treeSignature last != treeSignature sourceTree then
        throw <| IO.userError "ordered unary batch changed restored trees"
  | _ => throw <| IO.userError "unary batch did not preserve order and analysis statuses"

def testExpansionFailureKeepsSource : IO Unit := do
  let grammar ← requireGrammar
  let unaryConfig := { UnaryElimConfig.default with maxPaths := 0 }
  match ← NLP.runIO {} <|
      NLP.compileUnaryViterbiModelWith unaryConfig .default grammar "models/treebank" with
  | .error (.modelCorrupt source why) =>
      if source != "models/treebank" || !why.startsWith "unary expansion needs" then
        throw <| IO.userError "unary expansion failure lost its source or resource detail"
  | _ => throw <| IO.userError "impossible unary path budget was accepted"

def testInvalidUnaryWeight : IO Unit := do
  let bits : UInt64 := 0x8000000000000000
  let trees := #[sourceTree, .node 0 (.node 1 (.node 8 (.leaf 9) #[]) #[]) #[]]
  let .ok counted := Grammar.induce interner trees
    | throw <| IO.userError "unary-weight fixture induction failed"
  let invalid := counted.mapWeights fun count ↦
    if count.toNat == 2 then (⟨Float.ofBits bits⟩ : Vit) else 1
  match UnaryViterbiModel.compile invalid with
  | .error (.invalidUnaryWeight 0 value actual) =>
      if value.toBits != bits || actual != bits then
        throw <| IO.userError s!"invalid unary Float payload: expected={bits} actual={actual}"
  | _ => throw <| IO.userError "noncanonical unary weight was accepted"

private def invalidCountTwo (grammar : TreebankGrammar Count) : TreebankGrammar Vit :=
  let bits : UInt64 := 0x8000000000000000
  grammar.mapWeights fun count ↦
    if count.toNat == 2 then ⟨Float.ofBits bits⟩ else 1

private def repeatedBinaryTrees : Array Tree :=
  #[.node 0 (.node 1 (.node 2 (.leaf 4) #[]) #[.node 3 (.leaf 5) #[]]) #[],
    .node 0 (.node 1 (.node 2 (.leaf 6) #[]) #[.node 3 (.leaf 7) #[]])
      #[.node 8 (.leaf 9) #[]]]

private def repeatedLexicalTrees : Array Tree :=
  #[.node 0 (.node 1 (.node 2 (.leaf 4) #[]) #[]) #[],
    .node 0 (.node 3 (.node 2 (.leaf 4) #[]) #[]) #[]]

def testInvalidBaseWeightsKeepSourceOrdinals : IO Unit := do
  let .ok binary := Grammar.induce interner repeatedBinaryTrees
    | throw <| IO.userError "binary-weight fixture induction failed"
  match UnaryViterbiModel.compile (invalidCountTwo binary) with
  | .error (.invalidBinaryWeight 0 value bits) =>
      if value.toBits != bits || bits != 0x8000000000000000 then
        throw <| IO.userError "binary source-weight error lost its exact Float payload"
  | _ => throw <| IO.userError "invalid source binary weight was accepted or renumbered"
  let .ok lexical := Grammar.induce interner repeatedLexicalTrees
    | throw <| IO.userError "lexical-weight fixture induction failed"
  match UnaryViterbiModel.compile (invalidCountTwo lexical) with
  | .error (.invalidLexicalWeight 0 value bits) =>
      if value.toBits != bits || bits != 0x8000000000000000 then
        throw <| IO.userError "lexical source-weight error lost its exact Float payload"
  | _ => throw <| IO.userError "invalid source lexical weight was accepted or renumbered"

def testCancelled : IO Unit := do
  let grammar ← requireGrammar
  let .ok model := UnaryViterbiModel.compile grammar
    | throw <| IO.userError "cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.parseUnaryTree model #[4, 5])).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "unary Viterbi parser lost its cancellation reason"

#eval testPureFunctionalRoundTrip
#eval testPureRangeRoundTrip
#eval testEffectfulRoundTrip
#eval testNoAnalysisAndLengthPolicy
#eval testChartBudget
#eval testOrderedBatch
#eval testExpansionFailureKeepsSource
#eval testInvalidUnaryWeight
#eval testInvalidBaseWeightsKeepSourceOrdinals
#eval testCancelled

end NlpTests.Pipeline.Unary
