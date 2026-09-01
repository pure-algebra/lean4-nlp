import Nlp.Pipeline.Effects

/-!
# Effectful NLP runtime

`NLP.run` owns a cancellation tree for one top-level action. Pure models stay outside this module;
loaders and corpus orchestration use these helpers at the effect boundary.
-/

namespace Nlp.NLP

/-- Run with an explicitly supplied environment, useful when embedding NLP in another runtime. -/
@[inline] def runIn (env : Env) (action : NLP α) : EIO Fail α :=
  action env

/-- Run a top-level action and release its cancellation tree on every exit path. -/
def run (config : Config) (action : NLP α) : EIO Fail α := do
  let cancellation ← liftM <| Std.CancellationContext.new
  try
    action { config, cancellation }
  finally
    cancellation.cancel .cancel

/-- Enter the ordinary `IO` boundary without erasing typed `Fail` values. -/
def runIO (config : Config) (action : NLP α) : IO (Except Fail α) := do
  liftM <| (run config action).toBaseIO

/-- Abort at a cooperative cancellation boundary. -/
def checkCancelled : NLP Unit := do
  let env ← read
  match ← liftM <| env.cancellation.getCancellationReason with
  | some reason => throw <| .cancelled reason
  | none =>
      if ← liftM <| IO.checkCanceled then
        throw <| .cancelled .cancel

/-- Run an action under a local configuration change, preserving runtime capabilities. -/
@[inline] def withConfig (f : Config → Config) (action : NLP α) : NLP α :=
  fun env ↦ action { env with config := f env.config }

end Nlp.NLP
