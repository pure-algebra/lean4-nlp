import Nlp.Pipeline.TokenRegex

namespace NlpTests.Pipeline.TokenRegex

open Nlp Nlp.Pattern

private def sampleDoc (verb : String) : Doc [.tokens, .pos, .lemma, .ner] :=
  { text := s!"Ada {verb}"
    forms := #["Ada", verb]
    spans := #[⟨0, 3⟩, ⟨4, 4 + verb.utf8ByteSize⟩]
    pos := #["NNP", "VBZ"]
    lemma := #["ada", "write"]
    ner := #["PERSON", "O"] }

private def testCompileAndMatch : IO Unit := do
  let action : NLP (Analysis (Array Match)) := do
    let compiled ← NLP.compileTokenRegex "[ner:PERSON] [lemma:write]"
    NLP.matchTokenRegex compiled (sampleDoc "writes")
  match ← NLP.runIO {} action with
  | .ok (.ok #[matched]) =>
      unless matched.rule == 0 && matched.start == 0 && matched.stop == 2 do
        throw <| IO.userError "effectful TokensRegex returned the wrong absolute span"
  | _ => throw <| IO.userError "effectful TokensRegex did not match"

private def testCompileDiagnostic : IO Unit := do
  match ← NLP.runIO {} (NLP.compileTokenRegex "[word:a]*?" "rules/core.tokensregex") with
  | .error (.modelCorrupt source why) =>
      unless source == "rules/core.tokensregex" && why.contains "pattern bytes [8, 10)" &&
          why.contains "reluctant quantifiers" do
        throw <| IO.userError "TokensRegex compile diagnostic lost source or byte span"
  | _ => throw <| IO.userError "unsupported TokensRegex source was accepted"

private def testWorkSkip : IO Unit := do
  let action : NLP (Analysis (Array Match)) := do
    let compiled ← NLP.compileTokenRegex "[word:Ada]"
    NLP.matchTokenRegexAtWith "fixture" { maxWork := 0 } compiled (sampleDoc "writes")
  match ← NLP.runIO {} action with
  | .ok (.skipped (.workLimit required 0)) =>
      unless 0 < required do
        throw <| IO.userError "TokensRegex work skip reported an empty requirement"
  | _ => throw <| IO.userError "TokensRegex work limit was not a resource skip"

private def testMissingLayer : IO Unit := do
  let doc : Doc [.tokens] :=
    { text := "Ada"
      forms := #["Ada"]
      spans := #[⟨0, 3⟩] }
  let action : NLP (Analysis (Array Match)) := do
    let compiled ← NLP.compileTokenRegex "[lemma:ada]"
    NLP.matchTokenRegex compiled doc
  match ← NLP.runIO {} action with
  | .error (.invalidInput "TokensRegex input" why) =>
      unless why.contains "advertised lemma layer" do
        throw <| IO.userError "TokensRegex missing-layer diagnostic was unstable"
  | _ => throw <| IO.userError "TokensRegex accepted a missing lemma layer"

private def testCorpusOrder : IO Unit := do
  let action : NLP (Array (Analysis (Array Match))) := do
    let compiled ← NLP.compileTokenRegex "[word:Ada]"
    NLP.matchTokenRegexMany compiled #[sampleDoc "writes", sampleDoc "codes"]
  match ← NLP.runIO { numThreads := 2, parallelMinWeight := 1 } action with
  | .ok #[.ok #[first], .ok #[second]] =>
      unless first.start == 0 && second.start == 0 do
        throw <| IO.userError "TokensRegex corpus results changed coordinates"
  | _ => throw <| IO.userError "TokensRegex corpus traversal lost input order"

#eval testCompileAndMatch
#eval testCompileDiagnostic
#eval testWorkSkip
#eval testMissingLayer
#eval testCorpusOrder

end NlpTests.Pipeline.TokenRegex
