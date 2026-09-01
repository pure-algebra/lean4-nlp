import Nlp.Pipeline.Runtime

namespace NlpTests.Pipeline.Effects

open Nlp

example : Config := {}

example : Config := {
  numThreads := 4
  maxLen := 256
  parallelMinGrain := 128
  maxDedicatedThreads := 4
}

example : toString (Fail.invalidInput "fixture.conllu" "bad row") =
    "invalid input at fixture.conllu: bad row" := by
  rfl

def localConfig : NLP Nat :=
  NLP.withConfig (fun config ↦ { config with maxLen := 17 }) do
    return (← read).config.maxLen

def testRuntime : IO Unit := do
  match ← NLP.runIO {} localConfig with
  | .ok 17 => pure ()
  | _ => throw <| IO.userError "unexpected runtime result"

def testCancelled : IO Unit := do
  let cancellation ← liftM <| Std.CancellationContext.new
  cancellation.cancel .shutdown
  let env : Env := { config := {}, cancellation }
  match ← liftM <| (NLP.runIn env NLP.checkCancelled).toBaseIO with
  | .error (.cancelled .shutdown) => pure ()
  | _ => throw <| IO.userError "cancellation reason was not preserved"

#eval testRuntime
#eval testCancelled

end NlpTests.Pipeline.Effects
