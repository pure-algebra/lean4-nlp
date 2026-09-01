import Nlp.Core.Doc
import Nlp.IO.Fields

/-!
# Lossless CoNLL-U rows and sentence projection

The first layer in this module preserves comments and all ten raw row columns. In particular,
multiword-token ranges and empty nodes survive parsing and rendering. `ConlluSentence.toDoc` is a
separate, deliberately lossy projection: it keeps ordinary word rows, validates their dependency
heads, and synthesizes text separated by one ASCII space with UTF-8 byte spans.
-/

namespace Nlp.IO

/-- One lossless, ten-column CoNLL-U row.

The raw ID is retained so lexical spelling is preserved.
-/
structure ConlluRow where
  id : String
  form : String
  lemma : OptionalField
  upos : OptionalField
  xpos : OptionalField
  feats : OptionalField
  head : OptionalField
  deprel : OptionalField
  deps : OptionalField
  misc : OptionalField
  deriving Repr, DecidableEq, Inhabited

/-- Physical line-ending convention retained for byte-stable corpus rendering. -/
inductive ConlluLineEnding where
  | lf
  | crlf
  deriving Repr, DecidableEq, Inhabited

namespace ConlluLineEnding

@[inline] def render : ConlluLineEnding → String
  | .lf => "\n"
  | .crlf => "\r\n"

/-- Remove the carriage return, if any, left after splitting a physical line on LF. -/
def decode (rawLine : String) : String × ConlluLineEnding :=
  match rawLine.toList.reverse with
  | '\r' :: reversed => (String.ofList reversed.reverse, .crlf)
  | _ => (rawLine, .lf)

end ConlluLineEnding

/-- A sentence block, including its source comments and every row shape. -/
structure ConlluSentence where
  comments : Array String := #[]
  rows : Array ConlluRow := #[]
  lineEnding : ConlluLineEnding := .lf
  deriving Repr, DecidableEq, Inhabited

/-- Typed failures at the lossless syntax boundary and the projected document boundary. -/
inductive ConlluError where
  | wrongColumnCount (line : Nat) (found : Nat)
  | emptyField (line : Nat) (column : Nat)
  | commentAfterRow (line : Nat)
  | unexpectedBlank (line : Nat)
  | sentenceWithoutRows (line : Nat)
  | mixedLineEndings (line : Nat) (expected found : ConlluLineEnding)
  | missingFinalNewline
  | missingSentenceBoundary
  | malformedId (row : Nat) (value : String)
  | nonsequentialWordId (row : Nat) (expected found : Nat)
  | missingHead (row : Nat)
  | malformedHead (row : Nat) (value : String)
  | headOutOfRange (row head wordCount : Nat)
  | missingUpos (row : Nat)
  | missingDeprel (row : Nat)
  | noWordRows
  | docValidation (error : Doc.ValidationError)
  deriving Repr, DecidableEq, Inhabited

namespace ConlluRow

/-- The ten fields in their specified order. -/
def toFields (row : ConlluRow) : List String :=
  [row.id, row.form, row.lemma.render, row.upos.render, row.xpos.render,
    row.feats.render, row.head.render, row.deprel.render, row.deps.render, row.misc.render]

@[simp] theorem toFields_length (row : ConlluRow) : row.toFields.length = 10 := by
  simp [toFields]

/-- Every field is nonempty and contains no structural tab. -/
def WF (row : ConlluRow) : Prop :=
  ∀ field ∈ row.toFields, field.isEmpty = false ∧ '\t' ∉ field.toList

instance (row : ConlluRow) : Decidable row.WF := by
  unfold WF
  infer_instance

/-- Render one row without its terminating newline. -/
def render (row : ConlluRow) : String := joinFields row.toFields

/-- A well-formed row survives the delimiter layer exactly. -/
theorem splitFields_render (row : ConlluRow) (wellFormed : row.WF) :
    splitFields row.render = row.toFields := by
  apply splitFields_joinFields
  · intro field present
    exact (wellFormed field present).2
  · simp [toFields]

/-- Parse one row, reporting the physical source line in typed diagnostics. -/
def parse (lineNumber : Nat) (line : String) : Except ConlluError ConlluRow :=
  let fields := splitFields line
  match fields with
  | [idRaw, formRaw, lemmaRaw, uposRaw, xposRaw, featsRaw, headRaw, deprelRaw,
      depsRaw, miscRaw] =>
    match fields.findIdx? String.isEmpty with
    | some column => .error (.emptyField lineNumber (column + 1))
    | none =>
      let parsed : ConlluRow :=
        { id := idRaw, form := formRaw, lemma := OptionalField.parse lemmaRaw,
          upos := OptionalField.parse uposRaw, xpos := OptionalField.parse xposRaw,
          feats := OptionalField.parse featsRaw, head := OptionalField.parse headRaw,
          deprel := OptionalField.parse deprelRaw, deps := OptionalField.parse depsRaw,
          misc := OptionalField.parse miscRaw }
      .ok parsed
  | other => .error (.wrongColumnCount lineNumber other.length)

/-- Rendering then parsing recovers every well-formed semantic row. -/
theorem parse_render (row : ConlluRow) (wellFormed : row.WF) (lineNumber : Nat) :
    parse lineNumber row.render = .ok row := by
  have split : splitFields row.render = row.toFields := row.splitFields_render wellFormed
  have noEmpty : row.toFields.findIdx? String.isEmpty = none := by
    rw [List.findIdx?_eq_none_iff]
    intro field present
    exact (wellFormed field present).1
  simp only [toFields] at noEmpty
  rw [parse, split]
  simp only [toFields]
  rw [noEmpty]
  simp only [OptionalField.parse_render]

end ConlluRow

/-- Classified CoNLL-U ID shapes.

Rows retain the original string; this view is used by projection.
-/
inductive ConlluId where
  | word (index : Nat)
  | range (first last : Nat)
  | empty (anchor copy : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace ConlluId

private def strictDecimal? (raw : String) : Option Nat :=
  let chars := raw.toList
  if !chars.isEmpty && chars.all Char.isDigit then
    some (Nat.ofDigitChars 10 chars 0)
  else
    none

private def positiveNat? (raw : String) : Option Nat := do
  let value ← strictDecimal? raw
  if value = 0 then none else some value

/-- Parse and validate an ordinary, range, or empty-node ID. -/
def parse (raw : String) : Option ConlluId :=
  match raw.splitOn "-" with
  | [firstRaw, lastRaw] => do
    let first ← positiveNat? firstRaw
    let last ← positiveNat? lastRaw
    if first ≤ last then some (.range first last) else none
  | [whole] =>
    match whole.splitOn "." with
    | [anchorRaw, copyRaw] => do
      let anchor ← strictDecimal? anchorRaw
      let copy ← positiveNat? copyRaw
      some (.empty anchor copy)
    | [wordRaw] => do
      let index ← positiveNat? wordRaw
      some (.word index)
    | _ => none
  | _ => none

end ConlluId

namespace ConlluSentence

/-- Render a sentence with its comments, rows, and mandatory blank terminator. -/
def render (sentence : ConlluSentence) : String :=
  let newline := sentence.lineEnding.render
  let withComments :=
    sentence.comments.foldl (fun output comment => output ++ comment ++ newline) ""
  sentence.rows.foldl (fun output row => output ++ row.render ++ newline) withComments ++ newline

/-- Project ordinary token rows into a checked document.

Range and empty-node rows remain available in layer 1 but are skipped here. Since raw source text
is not reconstructible from rows alone, text is synthesized with one ASCII space between forms;
spans are half-open UTF-8 byte offsets into that synthesized text.
-/
def toDoc (sentence : ConlluSentence) :
    Except ConlluError (Doc [.dep, .lemma, .pos, .sents, .tokens]) := do
  let mut text := ""
  let mut spans : Array Span := #[]
  let mut forms : Array String := #[]
  let mut lemmas : Array String := #[]
  let mut positions : Array String := #[]
  let mut heads : Array Nat := #[]
  let mut relations : Array String := #[]
  let mut wordIds : Array (Nat × Nat) := #[]
  let mut sourcedHeads : Array (Nat × Nat) := #[]
  let mut rowNumber := 0
  for row in sentence.rows do
    rowNumber := rowNumber + 1
    match ConlluId.parse row.id with
    | none => throw (.malformedId rowNumber row.id)
    | some (.range _ _) | some (.empty _ _) => pure ()
    | some (.word wordId) =>
      let headRaw ←
        match row.head with
        | .missing => throw (.missingHead rowNumber)
        | .present value _ => pure value
      let head ←
        match ConlluId.strictDecimal? headRaw with
        | some value => pure value
        | none => throw (.malformedHead rowNumber headRaw)
      let upos ←
        match row.upos with
        | .missing => throw (.missingUpos rowNumber)
        | .present value _ => pure value
      let deprel ←
        match row.deprel with
        | .missing => throw (.missingDeprel rowNumber)
        | .present value _ => pure value
      let start := if forms.isEmpty then 0 else text.utf8ByteSize + 1
      text := if forms.isEmpty then row.form else text ++ " " ++ row.form
      let stop := start + row.form.utf8ByteSize
      spans := spans.push ⟨start, stop⟩
      forms := forms.push row.form
      lemmas := lemmas.push row.lemma.render
      positions := positions.push upos
      heads := heads.push head
      relations := relations.push deprel
      wordIds := wordIds.push (rowNumber, wordId)
      sourcedHeads := sourcedHeads.push (rowNumber, head)
  if forms.isEmpty then
    throw .noWordRows
  let mut expectedWordId := 1
  for (sourceRow, wordId) in wordIds do
    if wordId = expectedWordId then
      expectedWordId := expectedWordId + 1
    else
      throw (.nonsequentialWordId sourceRow expectedWordId wordId)
  for (sourceRow, head) in sourcedHeads do
    unless head ≤ forms.size do
      throw (.headOutOfRange sourceRow head forms.size)
  let document : Doc [.dep, .lemma, .pos, .sents, .tokens] :=
    { text, spans, forms, sentEnd := #[forms.size], pos := positions, lemma := lemmas,
      head := heads, deprel := relations }
  match document.checked with
  | .ok checked => pure checked
  | .error error => throw (.docValidation error)

end ConlluSentence

/-- Every sentence uses the same physical line-ending convention. -/
def UniformLineEndings (sentences : Array ConlluSentence) : Prop :=
  sentences.toList.Pairwise fun left right => left.lineEnding = right.lineEnding

instance (sentences : Array ConlluSentence) : Decidable (UniformLineEndings sentences) := by
  unfold UniformLineEndings
  infer_instance

/-- Render a corpus as canonical sentence blocks.

`parseConllu (renderConllu sentences)` requires `UniformLineEndings sentences`: the parser rejects
mixed physical styles instead of silently normalizing them. Uniformity is necessary, not a full
renderability predicate for arbitrary caller-built rows or comments. The main contract runs in the
safe direction: arrays returned by `parseConllu` retain their detected uniform style, and rendering
them reproduces canonical input byte-for-byte.
-/
def renderConllu (sentences : Array ConlluSentence) : String :=
  sentences.foldl (fun output sentence => output ++ sentence.render) ""

/-- Parse a canonical CoNLL-U corpus while preserving comments and all row shapes.

The parser requires the format's final blank sentence boundary. This makes the lossless
`renderConllu` round trip explicit instead of silently normalizing a truncated final sentence.
-/
def parseConllu (input : String) : Except ConlluError (Array ConlluSentence) := do
  if input.isEmpty then
    return #[]
  unless input.endsWith "\n" do
    throw .missingFinalNewline
  let lines := (input.splitOn "\n").dropLast
  let mut sentences : Array ConlluSentence := #[]
  let mut comments : Array String := #[]
  let mut rows : Array ConlluRow := #[]
  let mut detectedEnding : Option ConlluLineEnding := none
  let mut lineNumber := 0
  for rawLine in lines do
    lineNumber := lineNumber + 1
    let (line, lineEnding) := ConlluLineEnding.decode rawLine
    match detectedEnding with
    | none => detectedEnding := some lineEnding
    | some expected =>
      if expected = lineEnding then
        pure ()
      else
        throw (.mixedLineEndings lineNumber expected lineEnding)
    if line.isEmpty then
      if rows.isEmpty then
        if comments.isEmpty then
          throw (.unexpectedBlank lineNumber)
        else
          throw (.sentenceWithoutRows lineNumber)
      else
        sentences := sentences.push { comments, rows, lineEnding := detectedEnding.getD .lf }
        comments := #[]
        rows := #[]
    else if line.startsWith "#" then
      unless rows.isEmpty do
        throw (.commentAfterRow lineNumber)
      comments := comments.push line
    else
      let row ← ConlluRow.parse lineNumber line
      rows := rows.push row
  unless comments.isEmpty && rows.isEmpty do
    throw .missingSentenceBoundary
  return sentences

end Nlp.IO
