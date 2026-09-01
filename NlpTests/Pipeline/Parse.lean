import Nlp.Core.Score.Count
import Nlp.Core.Score.Recog
import Nlp.Pipeline.Parse

namespace NlpTests.Pipeline.Parse

open Nlp

private def countGrammar : CNF Count :=
  { bin := #[⟨0, 1, 2, 1⟩]
    lex := #[⟨1, 7, 1⟩, ⟨2, 8, 1⟩]
    start := 0
    nNT := 3 }

private def recogGrammar : CNF Recog :=
  { bin := #[⟨0, 1, 2, 1⟩]
    lex := #[⟨1, 7, 1⟩, ⟨2, 8, 1⟩]
    start := 0
    nNT := 3 }

private def invalidGrammar : CNF Count :=
  { bin := #[⟨0, 1, 3, 1⟩]
    lex := #[⟨1, 7, 1⟩]
    start := 0
    nNT := 3 }

def testCompileErrorMapping : IO Unit := do
  match ← NLP.runIO {} <| NLP.compileGrammar invalidGrammar "fixture/count.cnf" with
  | .error (.modelCorrupt source why) =>
      if source != "fixture/count.cnf" ||
          why != "binary rule 0 has nonterminals lhs=0, left=1, right=3; " ++
            "every nonterminal must be in [0, 3)" then
        throw <| IO.userError "compile error lost its source or rule details"
  | _ => throw <| IO.userError "invalid grammar was not mapped to Fail.modelCorrupt"

def testSingleCount : IO Unit := do
  match ← NLP.runIO {} do
    let compiled ← NLP.compileGrammar countGrammar
    NLP.parseSentence compiled #[7, 8]
  with
  | .ok (.ok count) =>
      if count.toNat != 1 then throw <| IO.userError "unexpected Count parse value"
  | _ => throw <| IO.userError "effectful Count parse failed"

def testExplicitCompileConfig : IO Unit := do
  match ← NLP.runIO {} <| NLP.compileGrammarWith { densePairCells := 8 } countGrammar with
  | .ok compiled =>
      if compiled.pairLayout != .sparse then
        throw <| IO.userError "effectful compilation ignored its pair-index configuration"
  | .error _ => throw <| IO.userError "effectful configured compilation failed"

def testSingleRecogNoAnalysis : IO Unit := do
  match ← NLP.runIO {} do
    let compiled ← NLP.compileGrammar recogGrammar
    NLP.parseSentence compiled #[7, 99]
  with
  | .ok .noAnalysis => pure ()
  | _ => throw <| IO.userError "zero recognition value was not reported as no analysis"

def testLengthPolicy : IO Unit := do
  match ← NLP.runIO { maxLen := 1 } do
    let compiled ← NLP.compileGrammar countGrammar
    NLP.parseSentence compiled #[7, 8]
  with
  | .ok (.skipped (.tooLong 2 1)) => pure ()
  | _ => throw <| IO.userError "sentence length policy was not preserved as analysis data"

def testChartBudget : IO Unit := do
  match ← NLP.runIO { maxChartEntries := 1 } do
    let compiled ← NLP.compileGrammar countGrammar
    NLP.parseSentence compiled #[7, 8]
  with
  | .ok (.skipped (.chartTooLarge 9 1)) => pure ()
  | _ => throw <| IO.userError "parser entered a chart beyond its allocation budget"

def testOrderedBatch : IO Unit := do
  let sentences : Array (Array Tok) := #[#[7, 8], #[7, 99], #[7, 8, 8], #[7, 8]]
  let config : Config := {
    numThreads := 4
    maxLen := 2
    parallelMinGrain := 1
    maxDedicatedThreads := 4
  }
  match ← NLP.runIO config do
    let compiled ← NLP.compileGrammar countGrammar
    NLP.parseSentences compiled sentences
  with
  | .ok #[.ok first, .noAnalysis, .skipped (.tooLong 3 2), .ok last] =>
      if first.toNat != 1 || last.toNat != 1 then
        throw <| IO.userError "batch parsing returned incorrect values"
  | _ => throw <| IO.userError "batch parsing did not preserve input order and statuses"

def testCancelled : IO Unit := do
  let .ok compiled := CompiledCNF.compile countGrammar
    | throw <| IO.userError "cancellation fixture did not compile"
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env (NLP.parseSentence compiled #[7, 8])).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "effectful parser lost its cancellation reason"

#eval testCompileErrorMapping
#eval testSingleCount
#eval testExplicitCompileConfig
#eval testSingleRecogNoAnalysis
#eval testLengthPolicy
#eval testChartBudget
#eval testOrderedBatch
#eval testCancelled

end NlpTests.Pipeline.Parse
