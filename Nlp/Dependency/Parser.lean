import Nlp.Dependency.Viterbi

/-!
# Reusable labeled projective dependency parsers

`Parser` validates a relation inventory once and retains a pure sentence scorer. Each sentence is
presented as a zero-copy view over aligned form and POS arrays. The scorer uses CoNLL-U arc
coordinates: head `0` is artificial root and real heads and dependents are 1-based within the
view. Scores are compiled and label-collapsed before the cubic Eisner kernel runs.

The scorer is intentionally caller-supplied. This module provides exact checked inference, not a
pretrained neural model or a claim of Stanford CoreNLP model compatibility.
-/

namespace Nlp.Dependency

/-- Why aligned form and POS columns could not form a sentence view. -/
inductive SentenceError where
  | columnCount (forms pos : Nat)
  | invalidRange (start stop tokens : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A zero-copy half-open sentence view over aligned document columns. -/
structure Sentence where
  private mk ::
  /-- Full document form column. -/
  forms : Array String
  /-- Full document POS column. -/
  pos : Array String
  /-- Inclusive flattened token offset. -/
  start : Nat
  /-- Exclusive flattened token offset. -/
  stop : Nat
  private aligned : pos.size = forms.size
  private ordered : start ≤ stop
  private bounded : stop ≤ forms.size

namespace Sentence

/-- Construct a checked zero-copy sentence view. -/
def ofRange (forms pos : Array String) (start stop : Nat) : Except SentenceError Sentence :=
  if aligned : pos.size = forms.size then
    if ordered : start ≤ stop then
      if bounded : stop ≤ forms.size then
        .ok (.mk forms pos start stop aligned ordered bounded)
      else
        .error (.invalidRange start stop forms.size)
    else
      .error (.invalidRange start stop forms.size)
  else
    .error (.columnCount forms.size pos.size)

/-- Construct a checked view over complete aligned columns. -/
@[inline] def ofArrays (forms pos : Array String) : Except SentenceError Sentence :=
  ofRange forms pos 0 forms.size

/-- Number of sentence-local real tokens. -/
@[inline] def size (sentence : Sentence) : Nat := sentence.stop - sentence.start

/-- Resolve a 1-based sentence-local token form. Artificial root `0` has no form. -/
@[inline] def form? (sentence : Sentence) (token : Nat) : Option String :=
  if 1 ≤ token && token ≤ sentence.size then
    sentence.forms[sentence.start + token - 1]?
  else
    none

/-- Resolve a 1-based sentence-local POS tag. Artificial root `0` has no POS tag. -/
@[inline] def pos? (sentence : Sentence) (token : Nat) : Option String :=
  if 1 ≤ token && token ≤ sentence.size then
    sentence.pos[sentence.start + token - 1]?
  else
    none

@[simp] theorem size_ofRange_eq_ok (forms pos : Array String) (start stop : Nat)
    (sentence : Sentence) (success : ofRange forms pos start stop = .ok sentence) :
    sentence.size = stop - start := by
  simp only [ofRange] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  rfl

end Sentence

/-- A pure labeled arc scorer over one checked sentence view. -/
abbrev Scorer := Sentence → Nat → Nat → Nat → Float

/-- A validated relation inventory paired with a pure sentence scorer. -/
structure Parser where
  private mk ::
  /-- Resource policy applied before every sentence-specific score compilation. -/
  scoreConfig : ArcScoreConfig
  /-- Ordered exact output relation names. -/
  relationNames : Array String
  /-- Relation ordinal reserved for the unique artificial-root arc. -/
  rootRelation : Nat
  /-- Pure scorer retained outside the cubic parsing loop. -/
  scorer : Scorer
  /-- Caller-supplied model identity retained by the effectful boundary. -/
  diagnosticSource : String

namespace Parser

/--
Validate a reusable parser's relation inventory under an explicit score-compilation policy.

A zero-token compilation exercises every inventory, capacity, and zero-allocation budget check
without invoking the scorer.
-/
def compileWith (config : ArcScoreConfig) (relationNames : Array String)
    (rootRelation : Nat) (scorer : Scorer) : Except ArcScoreError Parser := do
  let _ ← ArcScores.compileScorerWith config 0 relationNames rootRelation fun _ _ _ => 0.0
  return .mk config relationNames rootRelation scorer "in-memory dependency scorer"

/-- Compile a reusable parser under production score-compilation limits. -/
@[inline] def compile (relationNames : Array String) (rootRelation : Nat)
    (scorer : Scorer) : Except ArcScoreError Parser :=
  compileWith .default relationNames rootRelation scorer

/-- Replace only the diagnostic identity retained for effectful failures. -/
def withDiagnosticSource (parser : Parser) (source : String) : Parser :=
  .mk parser.scoreConfig parser.relationNames parser.rootRelation parser.scorer source

/-- Compile one sentence's labeled candidates into label-independent directed arcs. -/
def scoreSentence (parser : Parser) (sentence : Sentence) : Except ArcScoreError ArcScores :=
  ArcScores.compileScorerWith parser.scoreConfig sentence.size parser.relationNames
    parser.rootRelation (parser.scorer sentence)

/-- Parse one checked sentence through the pure functional API. -/
def parse? (parser : Parser) (sentence : Sentence) :
    Except ArcScoreError (Option Eisner.NamedResult) := do
  let arcs ← parser.scoreSentence sentence
  return Eisner.parseNamed? arcs

/-- Why aligned full columns could not be parsed. -/
inductive ArrayParseError where
  | sentence (cause : SentenceError)
  | scores (cause : ArcScoreError)
  deriving Repr

/-- Check full form/POS columns and parse them as one sentence. -/
def parseArrays? (parser : Parser) (forms pos : Array String) :
    Except ArrayParseError (Option Eisner.NamedResult) := do
  let sentence ←
    match Sentence.ofArrays forms pos with
    | .ok value => pure value
    | .error cause => throw <| .sentence cause
  match parser.parse? sentence with
  | .ok value => pure value
  | .error cause => throw <| .scores cause

end Parser

end Nlp.Dependency
