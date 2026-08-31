/-!
# Pipeline effects and partial analysis outcomes

Model loading and outer drivers use the zero-wrapper `NLP` transformer synonym. Loaded models run
purely on the hot path. Per-sentence inability to produce an analysis is data, not a program error.
-/

namespace Nlp

/-- Runtime configuration available to model loaders and corpus drivers. -/
structure Env where
  numThreads : Nat := 1
  maxLen : Nat := 400
  deriving Repr, DecidableEq, Inhabited

/-- Failures that abort loading or the outer pipeline driver. -/
inductive Fail where
  | modelMissing (path : String)
  | modelCorrupt (path : String) (why : String)
  | io (error : IO.Error)
  deriving Inhabited

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
