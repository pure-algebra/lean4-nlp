import Nlp.Pipeline.Constituency

/-! Functional and effectful named constituency document regression tests. -/

namespace NlpTests.Pipeline.Constituency

open Nlp Nlp.Grammar

private def interner : Interner :=
  { names := #["S", "NP", "N", "VP", "V", "dogs", "run", "<UNK>"] }

private def sentenceTree (noun : Word) : Tree :=
  .node 0 (.node 1 (.node 2 (.leaf noun) #[]) #[])
    #[.node 3 (.node 4 (.leaf 6) #[]) #[]]

private def sourceGrammar : Except InduceError (TreebankGrammar Vit) :=
  (Grammar.induce interner #[sentenceTree 5, sentenceTree 7]).map fun grammar ↦
    grammar.mapWeights fun _ ↦ (1 : Vit)

private def requireGrammar : IO (TreebankGrammar Vit) :=
  match sourceGrammar with
  | .ok grammar => pure grammar
  | .error cause => throw <| IO.userError s!"constituency fixture induction failed: {repr cause}"

private def requireModel : IO ConstituencyModel := do
  let grammar ← requireGrammar
  match ConstituencyModel.compile grammar "<UNK>" with
  | .ok model => pure model
  | .error cause => throw <| IO.userError s!"constituency fixture compile failed: {repr cause}"

private def document : Doc [.sents, .tokens] :=
  { text := "dogs run cats run"
    spans := #[⟨0, 4⟩, ⟨5, 8⟩, ⟨9, 13⟩, ⟨14, 17⟩]
    forms := #["dogs", "run", "cats", "run"]
    sentEnd := #[2, 4] }

private def dogsDocument : Doc [.sents, .tokens] :=
  { text := "dogs run"
    spans := #[⟨0, 4⟩, ⟨5, 8⟩]
    forms := #["dogs", "run"]
    sentEnd := #[2] }

private def catsDocument : Doc [.sents, .tokens] :=
  { text := "cats run"
    spans := #[⟨0, 4⟩, ⟨5, 8⟩]
    forms := #["cats", "run"]
    sentEnd := #[2] }

private def birdsDocument : Doc [.sents, .tokens] :=
  { text := "birds run"
    spans := #[⟨0, 5⟩, ⟨6, 9⟩]
    forms := #["birds", "run"]
    sentEnd := #[2] }

private def expectedSpans : Array (String × Nat × Nat) :=
  #[(("S", 0, 2)), (("NP", 0, 1)), (("N", 0, 1)),
    (("VP", 1, 2)), (("V", 1, 2))]

def testPureNamedAndOov : IO Unit := do
  let model ← requireModel
  if model.encode "dogs" != 5 || model.encode "NP" != 7 || model.encode "cats" != 7 then
    throw <| IO.userError "constituency lexical lookup admitted a category-only spelling"
  match model.parseForms? #["cats", "run"] with
  | .ok (some tree) =>
      if tree.yieldForms != #["cats", "run"] || tree.spans != expectedSpans ||
          !tree.categoriesNonempty then
        throw <| IO.userError "named parsing changed an OOV surface or constituent span"
  | _ => throw <| IO.userError "valid OOV-backed sentence did not parse"

def testPureDocument : IO Unit := do
  let model ← requireModel
  match model.parseDocument? document with
  | .ok (some output) =>
      if output.parse.size != 2 || output.parse[0]!.yieldForms != #["dogs", "run"] ||
          output.parse[1]!.yieldForms != #["cats", "run"] ||
          !decide output.SemanticWF || output.sentenceCubicWork != 16 then
        throw <| IO.userError "pure constituency document output violated exact alignment"
  | _ => throw <| IO.userError "valid two-sentence constituency document did not parse"

def testRangeAndAssemblyFailures : IO Unit := do
  let model ← requireModel
  let padded := #["outside", "cats", "run"]
  match model.parseFormsRange? padded 1 99 with
  | .ok (some tree) =>
      if tree.yieldForms != #["cats", "run"] then
        throw <| IO.userError "clamped constituency range changed its exact surface yield"
  | _ => throw <| IO.userError "valid clamped constituency range did not parse"
  match model.parseFormsRange? padded 3 1 with
  | .ok none => pure ()
  | _ => throw <| IO.userError "reversed constituency range did not normalize to empty input"
  match model.parseEncodedRange? #["dogs"] #[5, 6] 0 1 with
  | .error (.columnCount 1 2) => pure ()
  | _ => throw <| IO.userError "misaligned constituency columns were accepted"
  match model.resolveTreeRange #["dogs", "run"] #[5, 6] 0 2 (.leaf 5) with
  | .error (.terminalCount 2 1) => pure ()
  | _ => throw <| IO.userError "restored constituency width mismatch was accepted"
  match ConstituencyModel.assembleDocument document #[.leaf "dogs"] with
  | .error (.sentenceCount 2 1) => pure ()
  | _ => throw <| IO.userError "constituency assembly accepted the wrong tree count"
  match ConstituencyModel.assembleDocument document #[.leaf "dogs", .leaf "cats"] with
  | .error (.output (.parseYieldMismatch 0 _ _)) => pure ()
  | _ => throw <| IO.userError "constituency assembly accepted a wrong sentence yield"

def testCompileFailures : IO Unit := do
  let grammar ← requireGrammar
  if grammar.symbols != interner.names then
    throw <| IO.userError "treebank grammar did not retain its exact source namespace"
  match ConstituencyModel.compile grammar "missing" with
  | .error (.missingOovSymbol "missing") => pure ()
  | _ => throw <| IO.userError "missing constituency OOV symbol was accepted"
  match ConstituencyModel.compile grammar "S" with
  | .error (.oovNotLexical "S" 0) => pure ()
  | _ => throw <| IO.userError "category-only constituency OOV symbol was accepted"

def testNoAnalysisAndPolicy : IO Unit := do
  let grammar ← requireGrammar
  let reversed : Doc [.sents, .tokens] :=
    { document with
      text := "run dogs"
      spans := #[⟨0, 3⟩, ⟨4, 8⟩]
      forms := #["run", "dogs"]
      sentEnd := #[2] }
  match ← NLP.runIO {} do
    let model ← NLP.compileConstituencyModel grammar "<UNK>"
    NLP.parseConstituency model reversed
  with
  | .ok .noAnalysis => pure ()
  | _ => throw <| IO.userError "unparseable constituency sentence was not data"
  match ← NLP.runIO { maxLen := 1 } do
    let model ← NLP.compileConstituencyModel grammar "<UNK>"
    NLP.parseConstituency model document
  with
  | .ok (.skipped (.tooLong 2 1)) => pure ()
  | _ => throw <| IO.userError "constituency sentence-length policy was not applied"
  match ← NLP.runIO { maxChartEntries := 1 } do
    let model ← NLP.compileConstituencyModel grammar "<UNK>"
    NLP.parseConstituency model dogsDocument
  with
  | .ok (.skipped (.chartTooLarge required 1)) =>
      if required != 15 then
        throw <| IO.userError s!"unexpected constituency chart size: {required}"
  | _ => throw <| IO.userError "constituency chart-allocation policy was not applied"

def testEffectfulOrderedBatch : IO Unit := do
  let grammar ← requireGrammar
  let config : Config :=
    { numThreads := 3, parallelMinWeight := 1, maxDedicatedThreads := 3 }
  match ← NLP.runIO config do
    let model ← NLP.compileConstituencyModel grammar "<UNK>"
    NLP.parseConstituencyManyWithMinWork 1 model
      #[dogsDocument, catsDocument, birdsDocument]
  with
  | .ok #[.ok first, .ok second, .ok third] =>
      let yields := #[first.parse[0]!.yieldForms, second.parse[0]!.yieldForms,
        third.parse[0]!.yieldForms]
      if yields != #[#["dogs", "run"], #["cats", "run"], #["birds", "run"]] ||
          !decide first.SemanticWF || !decide second.SemanticWF ||
          !decide third.SemanticWF then
        throw <| IO.userError "constituency batch lost order or checked trees"
  | .ok _ => throw <| IO.userError "constituency batch changed result cardinality or status"
  | .error cause => throw <| IO.userError s!"constituency batch failed: {cause}"

def testCancelled : IO Unit := do
  let model ← requireModel
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.parseConstituency model document)).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "constituency parsing lost its cancellation reason"

#eval testPureNamedAndOov
#eval testPureDocument
#eval testRangeAndAssemblyFailures
#eval testCompileFailures
#eval testNoAnalysisAndPolicy
#eval testEffectfulOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.Constituency
