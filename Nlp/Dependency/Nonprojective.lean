import Nlp.Dependency.Arborescence
import Nlp.Dependency.Parser
import Nlp.Core.Doc

/-!
# Functional nonprojective dependency parsing

This additive bridge reuses a validated `Dependency.Parser` and its label-collapsed `ArcScores`
with the single-root arborescence decoder. Existing projective parser operations remain unchanged.
Sentence and document results retain sentence-local CoNLL-U head coordinates.
-/

namespace Nlp.Dependency.Parser

/-- A score compiler or nonprojective kernel rejected one checked sentence. -/
inductive NonprojectiveError where
  | scores (cause : ArcScoreError)
  | kernel (cause : Arborescence.KernelError)
  deriving Repr

/-- Why aligned full columns could not be decoded nonprojectively. -/
inductive NonprojectiveArrayError where
  | sentence (cause : SentenceError)
  | scores (cause : ArcScoreError)
  | kernel (cause : Arborescence.KernelError)
  deriving Repr

/-- A checked document could not be converted into nonprojective dependency output. -/
inductive NonprojectiveDocumentError where
  | input (cause : Doc.SemanticError)
  | sentenceView (sentence start stop : Nat) (cause : SentenceError)
  | scores (sentence start stop : Nat) (cause : ArcScoreError)
  | kernel (sentence start stop : Nat) (cause : Arborescence.KernelError)
  | sentenceCount (expected found : Nat)
  | resultSize (sentence expected heads relations : Nat)
  | output (cause : Doc.SemanticError)
  deriving Repr

/-- Quadratic scheduling work implied by one document's advertised sentence ranges. -/
def nonprojectiveDocumentWork (doc : Doc available) : Nat :=
  doc.sentenceRanges.foldl (init := 0) fun total range ↦
    let length := range.2 - range.1
    total + length * length

/-- Decode one checked sentence with an explicit nonprojective workspace policy. -/
def parseNonprojectiveWith? (parser : Parser) (config : Arborescence.KernelConfig)
    (sentence : Sentence) :
    Except NonprojectiveError (Option Arborescence.NamedResult) := do
  let arcs ←
    match parser.scoreSentence sentence with
    | .ok value => pure value
    | .error cause => throw <| .scores cause
  match Arborescence.parseNamedWith? config arcs with
  | .ok value => pure value
  | .error cause => throw <| .kernel cause

/-- Decode one checked sentence under the production nonprojective workspace policy. -/
def parseNonprojective? (parser : Parser) (sentence : Sentence) :
    Except NonprojectiveError (Option Arborescence.NamedResult) :=
  parser.parseNonprojectiveWith? .default sentence

/-- Check complete form/POS columns and decode them with an explicit workspace policy. -/
def parseNonprojectiveArraysWith? (parser : Parser) (config : Arborescence.KernelConfig)
    (forms pos : Array String) :
    Except NonprojectiveArrayError (Option Arborescence.NamedResult) := do
  let sentence ←
    match Sentence.ofArrays forms pos with
    | .ok value => pure value
    | .error cause => throw <| .sentence cause
  match parser.parseNonprojectiveWith? config sentence with
  | .ok value => pure value
  | .error (.scores cause) => throw <| .scores cause
  | .error (.kernel cause) => throw <| .kernel cause

/-- Check complete form/POS columns and decode them under production workspace limits. -/
def parseNonprojectiveArrays? (parser : Parser) (forms pos : Array String) :
    Except NonprojectiveArrayError (Option Arborescence.NamedResult) :=
  parser.parseNonprojectiveArraysWith? .default forms pos

/-- Validate and assemble aligned sentence-local nonprojective results into one document. -/
def assembleNonprojectiveDocument (doc : Doc available)
    (results : Array Arborescence.NamedResult) :
    Except NonprojectiveDocumentError (Doc (.dep :: available)) := do
  let ranges := doc.sentenceRanges
  if results.size != ranges.size then
    throw <| .sentenceCount ranges.size results.size
  let mut heads := Array.emptyWithCapacity doc.size
  let mut relations := Array.emptyWithCapacity doc.size
  for sentence in [0:ranges.size] do
    let range := ranges[sentence]!
    let expected := range.2 - range.1
    let some result := results[sentence]?
      | throw <| .sentenceCount ranges.size results.size
    if result.heads.size != expected || result.relations.size != expected then
      throw <| .resultSize sentence expected result.heads.size result.relations.size
    for head in result.heads do
      heads := heads.push head
    for relation in result.relations do
      relations := relations.push relation
  let output : Doc (.dep :: available) := { doc with head := heads, deprel := relations }
  match output.checkedSemantic with
  | .ok checked => pure checked
  | .error cause => throw <| .output cause

/-- Decode every advertised sentence with an explicit nonprojective workspace policy. -/
def parseNonprojectiveDocumentWith? (parser : Parser)
    (config : Arborescence.KernelConfig) (doc : Doc available)
    (_requirements : Sub [.tokens, .pos] available := by decide) :
    Except NonprojectiveDocumentError (Option (Doc (.dep :: available))) := do
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause => throw <| .input cause
  let ranges := checked.sentenceRanges
  let mut results := Array.emptyWithCapacity ranges.size
  for sentence in [0:ranges.size] do
    let (start, stop) := ranges[sentence]!
    let view ←
      match Sentence.ofRange checked.forms checked.pos start stop with
      | .ok value => pure value
      | .error cause => throw <| .sentenceView sentence start stop cause
    let result ←
      match parser.parseNonprojectiveWith? config view with
      | .ok value => pure value
      | .error (.scores cause) => throw <| .scores sentence start stop cause
      | .error (.kernel cause) => throw <| .kernel sentence start stop cause
    match result with
    | none => return none
    | some value => results := results.push value
  return some (← assembleNonprojectiveDocument checked results)

/-- Decode every advertised sentence under production nonprojective workspace limits. -/
def parseNonprojectiveDocument? (parser : Parser) (doc : Doc available)
    (requirements : Sub [.tokens, .pos] available := by decide) :
    Except NonprojectiveDocumentError (Option (Doc (.dep :: available))) :=
  parser.parseNonprojectiveDocumentWith? .default doc requirements

end Nlp.Dependency.Parser
