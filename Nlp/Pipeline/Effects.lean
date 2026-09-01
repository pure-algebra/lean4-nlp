import Std.Sync.CancellationContext

/-!
# Pipeline effects and analysis outcomes

Model loading and outer drivers use the zero-wrapper `NLP` transformer synonym. Loaded models run
purely on the hot path. Per-sentence inability to produce an analysis is data, not a program error.
-/

namespace Nlp

/-- Stable runtime knobs shared by model loaders and corpus drivers. -/
structure Config where
  /-- Requested top-level worker count; zero selects the available hardware count. -/
  numThreads : Nat := 1
  /-- Maximum token length accepted by bounded model kernels. -/
  maxLen : Nat := 400
  /-- Minimum item count in each chunk of a count-balanced traversal. -/
  parallelMinGrain : Nat := 65536
  /-- Minimum normalized aggregate weight in each chunk of a weighted traversal. -/
  parallelMinWeight : Nat := 65536
  /-- Hard ceiling on dedicated worker threads created by one outer traversal. -/
  maxDedicatedThreads : Nat := 8
  deriving Repr, DecidableEq, Inhabited

/-- Failures that abort loading or the outer pipeline driver. -/
inductive Fail where
  | modelMissing (path : String)
  | modelCorrupt (path : String) (why : String)
  | invalidConfig (why : String)
  | invalidInput (location : String) (why : String)
  | cancelled (reason : Std.CancellationReason)
  | io (error : IO.Error)
  deriving Inhabited

namespace Fail

/-- Stable human-readable rendering for CLI and embedding boundaries. -/
def describe : Fail → String
  | .modelMissing path => s!"model not found: {path}"
  | .modelCorrupt path why => s!"invalid model {path}: {why}"
  | .invalidConfig why => s!"invalid NLP configuration: {why}"
  | .invalidInput location why => s!"invalid input at {location}: {why}"
  | .cancelled reason => s!"NLP action cancelled: {reason}"
  | .io error => toString error

instance : ToString Fail := ⟨describe⟩

end Fail

/-- Runtime capabilities. `parallelDepth` prevents nested dedicated-thread fan-out. -/
structure Env where
  config : Config
  cancellation : Std.CancellationContext
  parallelDepth : Nat := 0

/-- A transformer synonym, not a structure wrapper, so binds can inline and fuse. -/
abbrev NLP := ReaderT Env (EIO Fail)

/-- Why an individual sentence was intentionally not analysed. -/
inductive SkipReason where
  | tooLong (tokens limit : Nat)
  | outOfVocabulary
  | disabled
  | timedOut
  deriving Repr, DecidableEq, Inhabited

/-- The explicit per-sentence result of an annotator that may not produce a value. -/
inductive Analysis (T : Type) where
  | ok (value : T)
  | skipped (reason : SkipReason)
  | noAnalysis
  deriving Repr, DecidableEq, Inhabited

namespace Analysis

/-- Map a pure function over a successful analysis while preserving non-results. -/
@[inline] def map (f : α → β) : Analysis α → Analysis β
  | .ok value => .ok (f value)
  | .skipped reason => .skipped reason
  | .noAnalysis => .noAnalysis

end Analysis

end Nlp
