import Nlp.IO.Fields

/-!
# CoNLL-U sentence reader

A total, spec'd reader and printer for the CoNLL-U format of Universal Dependencies
(<https://universaldependencies.org/format.html>; local extract:
`reference/data/formats/conllu.md`). A file is a sequence of sentence blocks separated by blank
lines; a block is `#`-prefixed comment lines followed by token lines; a token line is exactly ten
tab-separated fields: ID, FORM, LEMMA, UPOS, XPOS, FEATS, HEAD, DEPREL, DEPS, MISC.

This is layer 1 in the sense of `docs/plan/near-term.md` §2: rows are represented structurally
faithfully — multiword-token ranges (`3-4`) and empty nodes (`3.1`) are constructors of
`CoNLLUId`, not dropped — and the reserved `_` of the seven optional columns is interpreted
through the proved `OptionalField` codec of `Nlp.IO.Fields`. Interpretation into `Doc`/trees is a
separate, later layer.

## Round-trip theorems

* `parseDecimal?_toDigits` — the strict decimal sub-parser inverts `Nat.toDigits`;
* `CoNLLUId.parse_render` — the ID sub-parser inverts the ID printer on all three ID shapes;
* `parseHead_renderHead` — the HEAD sub-parser inverts the HEAD printer;
* `parseRow_renderRow` — the full row parser inverts the row printer on `CoNLLURow.WF` rows.

The reverse composition `renderRow ∘ parseRow` is *not* the identity on raw lines: parsing
canonicalizes numerals (`07` parses to the same ID as `7`), and the format itself is not injective
on `_` (a literal-underscore LEMMA is indistinguishable from a missing one — the spec resolves
this by fiat, see `reference/data/formats/conllu.md` §7). The sentence-level composition
`parseSentences ∘ renderSentences` also discards nothing (comments are already gone after
`parseSentences`) and is exercised by `native_decide` tests in `NlpTests/IO/CoNLLU.lean`.
-/

namespace Nlp.IO

/-! ### Strict decimal numerals

CoNLL-U indices are plain decimal digit runs. `String.toNat?` in current Lean accepts `_` digit
separators, so it is too liberal here; this parser accepts exactly nonempty all-digit strings.
-/

/-- Parse a strict decimal numeral: `some` exactly on nonempty strings of ASCII digits.
Leading zeros are accepted (`07` parses to `7`), so this is a left inverse of printing, not a
bijection. -/
def parseDecimal? (chars : List Char) : Option Nat :=
  if !chars.isEmpty && chars.all Char.isDigit then some (Nat.ofDigitChars 10 chars 0) else none

/-- A character that is not an ASCII digit never occurs in a printed decimal numeral. -/
theorem not_mem_toDigits_of_isDigit_eq_false {c : Char} (h : c.isDigit = false) {n : Nat} :
    c ∉ Nat.toDigits 10 n := fun mem ↦ by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) mem
  rw [h] at this
  exact Bool.false_ne_true this

/-- The strict decimal parser inverts `Nat.toDigits`. -/
theorem parseDecimal?_toDigits (n : Nat) : parseDecimal? (Nat.toDigits 10 n) = some n := by
  have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
  have hall : (Nat.toDigits 10 n).all Char.isDigit = true :=
    List.all_eq_true.mpr fun c hc ↦ Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp [parseDecimal?, hne, hall]

/-! ### The three ID shapes -/

/-- The ID column of a CoNLL-U token line, structurally faithful to the three shapes the format
allows: a word index `7`, a multiword-token range `7-8`, or an empty-node index `7.1`. -/
inductive CoNLLUId where
  /-- A syntactic word, 1-based index within its sentence: `7`. -/
  | word (index : Nat)
  /-- A multiword (surface) token covering words `first` through `last`: `7-8`. -/
  | range (first last : Nat)
  /-- An empty node for the enhanced graph, the `sub`-th inserted after word `anchor`: `7.1`. -/
  | emptyNode (anchor sub : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace CoNLLUId

/-- The character-level rendering of an ID; the digit runs come from `Nat.toDigits`. -/
def renderChars : CoNLLUId → List Char
  | .word index => Nat.toDigits 10 index
  | .range first last => Nat.toDigits 10 first ++ '-' :: Nat.toDigits 10 last
  | .emptyNode anchor sub => Nat.toDigits 10 anchor ++ '.' :: Nat.toDigits 10 sub

/-- Render an ID in canonical CoNLL-U form: `7`, `7-8`, or `7.1`. -/
def render (id : CoNLLUId) : String := String.ofList id.renderChars

/-- Parse an ID field. The separator (`-` or `.`) decides the shape; each numeral is strict
decimal. Shape constraints beyond syntax (`first ≤ last`, `1 ≤ sub`) belong to a later
validation layer, mirroring how the format spec separates syntax from tree well-formedness. -/
def parse (field : String) : Except String CoNLLUId :=
  match field.toList.splitOn '-' with
  | [firstPart, lastPart] =>
    match parseDecimal? firstPart, parseDecimal? lastPart with
    | some first, some last => .ok (.range first last)
    | _, _ => .error s!"malformed multiword-token range ID `{field}`"
  | [whole] =>
    match whole.splitOn '.' with
    | [anchorPart, subPart] =>
      match parseDecimal? anchorPart, parseDecimal? subPart with
      | some anchor, some sub => .ok (.emptyNode anchor sub)
      | _, _ => .error s!"malformed empty-node ID `{field}`"
    | [digitRun] =>
      match parseDecimal? digitRun with
      | some index => .ok (.word index)
      | none => .error s!"malformed word ID `{field}`"
    | _ => .error s!"malformed ID `{field}`: more than one `.`"
  | _ => .error s!"malformed ID `{field}`: more than one `-`"

/-- The ID parser inverts the ID printer on every ID value. -/
theorem parse_render (id : CoNLLUId) : parse id.render = .ok id := by
  have hdash : ∀ n : Nat, '-' ∉ Nat.toDigits 10 n := fun n ↦
    not_mem_toDigits_of_isDigit_eq_false (by decide)
  have hdot : ∀ n : Nat, '.' ∉ Nat.toDigits 10 n := fun n ↦
    not_mem_toDigits_of_isDigit_eq_false (by decide)
  cases id with
  | word index =>
    simp only [parse, render, renderChars, String.toList_ofList,
      List.splitOn_eq_singleton (hdash index), List.splitOn_eq_singleton (hdot index),
      parseDecimal?_toDigits]
  | range first last =>
    simp only [parse, render, renderChars, String.toList_ofList,
      List.splitOn_append_cons_self_of_not_mem (hdash first),
      List.splitOn_eq_singleton (hdash last), parseDecimal?_toDigits]
  | emptyNode anchor sub =>
    have hwhole : '-' ∉ Nat.toDigits 10 anchor ++ '.' :: Nat.toDigits 10 sub := by
      simp only [List.mem_append, List.mem_cons]
      rintro (h | h | h)
      · exact hdash anchor h
      · exact absurd h (by decide)
      · exact hdash sub h
    simp only [parse, render, renderChars, String.toList_ofList,
      List.splitOn_eq_singleton hwhole,
      List.splitOn_append_cons_self_of_not_mem (hdot anchor),
      List.splitOn_eq_singleton (hdot sub), parseDecimal?_toDigits]

/-- Rendered IDs never contain a tab, so they survive the tab-delimited field layer. -/
theorem render_tab_free (id : CoNLLUId) : '\t' ∉ id.render.toList := by
  have hdigits : ∀ n : Nat, '\t' ∉ Nat.toDigits 10 n := fun n ↦
    not_mem_toDigits_of_isDigit_eq_false (by decide)
  cases id with
  | word index =>
    simp only [render, renderChars, String.toList_ofList]
    exact hdigits index
  | range first last =>
    simp only [render, renderChars, String.toList_ofList, List.mem_append, List.mem_cons]
    rintro (h | h | h)
    · exact hdigits first h
    · exact absurd h (by decide)
    · exact hdigits last h
  | emptyNode anchor sub =>
    simp only [render, renderChars, String.toList_ofList, List.mem_append, List.mem_cons]
    rintro (h | h | h)
    · exact hdigits anchor h
    · exact absurd h (by decide)
    · exact hdigits sub h

end CoNLLUId

/-! ### The HEAD column -/

/-- Render a HEAD value: `_` for missing (multiword tokens and empty nodes), otherwise the
decimal head index, where `0` marks the sentence root. -/
def renderHead : Option Nat → String
  | none => "_"
  | some index => String.ofList (Nat.toDigits 10 index)

/-- Parse a HEAD field: `_` is missing, otherwise a strict decimal index. -/
def parseHead (field : String) : Except String (Option Nat) :=
  if field = "_" then .ok none
  else
    match parseDecimal? field.toList with
    | some index => .ok (some index)
    | none => .error s!"malformed HEAD `{field}`: expected `_` or a decimal index"

/-- The HEAD parser inverts the HEAD printer. -/
theorem parseHead_renderHead (head : Option Nat) : parseHead (renderHead head) = .ok head := by
  cases head with
  | none => simp [renderHead, parseHead]
  | some index =>
    have hne : String.ofList (Nat.toDigits 10 index) ≠ "_" := fun h ↦
      Nat.underscore_not_in_toDigits (n := index) (by
        have := congrArg String.toList h
        rw [String.toList_ofList] at this
        rw [this]
        exact List.mem_singleton_self '_')
    simp only [renderHead, parseHead, if_neg hne, String.toList_ofList, parseDecimal?_toDigits]

/-- Rendered HEAD values never contain a tab. -/
theorem renderHead_tab_free (head : Option Nat) : '\t' ∉ (renderHead head).toList := by
  cases head with
  | none => simp only [renderHead]; decide
  | some index =>
    simp only [renderHead, String.toList_ofList]
    exact not_mem_toDigits_of_isDigit_eq_false (by decide)

/-! ### Rows -/

/-- One CoNLL-U token line. ID and HEAD are parsed (cheap and unambiguous); FORM is raw (it is
never `_`-optional); the seven remaining columns go through the `OptionalField` codec, which
represents the reserved `_` faithfully. Everything else about a column's internal syntax
(FEATS `|`-lists, DEPS pairs, MISC key-values) is left to later layers. -/
structure CoNLLURow where
  /-- ID: word index, multiword-token range, or empty-node index. -/
  id : CoNLLUId
  /-- FORM: word form or punctuation symbol, kept raw. -/
  form : String
  /-- LEMMA: lemma or stem of the word form, `_` when missing. -/
  lemma : OptionalField
  /-- UPOS: universal POS tag, `_` on multiword-token lines. -/
  upos : OptionalField
  /-- XPOS: language-specific POS tag, `_` when missing. -/
  xpos : OptionalField
  /-- FEATS: `|`-joined morphological features, `_` when empty. -/
  feats : OptionalField
  /-- HEAD: head word index (`0` for root), `none` (`_`) on multiword tokens and empty nodes. -/
  head : Option Nat
  /-- DEPREL: dependency relation to HEAD, `_` when HEAD is missing. -/
  deprel : OptionalField
  /-- DEPS: `|`-joined enhanced dependencies, `_` when missing. -/
  deps : OptionalField
  /-- MISC: `|`-joined open key-value annotations, `_` when empty. -/
  misc : OptionalField
  deriving Repr, DecidableEq, Inhabited

/-- A string usable verbatim as one field of a tab-separated line: nonempty and free of the
delimiters tab, newline, and carriage return. -/
def cleanField (field : String) : Bool :=
  !field.isEmpty && field.toList.all fun c ↦ c != '\t' && c != '\n' && c != '\r'

/-- Clean fields contain no tab, so `splitFields` cannot cut them. -/
theorem tab_free_of_cleanField {field : String} (h : cleanField field = true) :
    '\t' ∉ field.toList := fun mem ↦ by
  rw [cleanField, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 '\t' mem
  simp at this

/-- Decidable well-formedness of a row: every rendered string column is a clean field. The ID
and HEAD columns need no condition — their renderers only produce digits, `-`, `.`, and `_`. -/
def CoNLLURow.wf (row : CoNLLURow) : Bool :=
  cleanField row.form && cleanField row.lemma.render && cleanField row.upos.render &&
    cleanField row.xpos.render && cleanField row.feats.render &&
    cleanField row.deprel.render && cleanField row.deps.render && cleanField row.misc.render

/-- Well-formedness of a row as a proposition; the hypothesis of the row round trip.

Beyond what the round trip needs (tab-freeness), `WF` also demands nonempty, newline-free
fields, which is what the sentence layer needs: a rendered `WF` row is one line, is not blank,
and does not start with `#` (its first field renders from `CoNLLUId`, hence starts with a
digit). -/
def CoNLLURow.WF (row : CoNLLURow) : Prop := row.wf = true

instance (row : CoNLLURow) : Decidable row.WF := inferInstanceAs (Decidable (_ = true))

/-- Render a row as one tab-separated CoNLL-U line (without terminator). -/
def renderRow (row : CoNLLURow) : String :=
  joinFields [row.id.render, row.form, row.lemma.render, row.upos.render, row.xpos.render,
    row.feats.render, renderHead row.head, row.deprel.render, row.deps.render, row.misc.render]

/-- Parse one CoNLL-U token line: exactly ten tab-separated fields, with ID and HEAD parsed
strictly and the optional columns interpreted through `OptionalField.parse`. Total; every
failure is a descriptive `Except.error`. -/
def parseRow (line : String) : Except String CoNLLURow :=
  match splitFields line with
  | [idF, formF, lemmaF, uposF, xposF, featsF, headF, deprelF, depsF, miscF] =>
    match CoNLLUId.parse idF, parseHead headF with
    | .ok id, .ok head =>
      .ok { id, form := formF, lemma := OptionalField.parse lemmaF,
            upos := OptionalField.parse uposF, xpos := OptionalField.parse xposF,
            feats := OptionalField.parse featsF, head,
            deprel := OptionalField.parse deprelF, deps := OptionalField.parse depsF,
            misc := OptionalField.parse miscF }
    | .error e, _ => .error e
    | _, .error e => .error e
  | fields => .error s!"expected 10 tab-separated fields, found {fields.length}"

/-- **Row round trip**: parsing a rendered well-formed row recovers the row exactly.

The proof composes the proved pieces: `splitFields_joinFields` recovers the ten fields (their
tab-freeness comes from `WF` for the string columns and from the renderers for ID and HEAD),
then `CoNLLUId.parse_render`, `parseHead_renderHead`, and `OptionalField.parse_render` recover
each column. -/
theorem parseRow_renderRow (row : CoNLLURow) (wf : row.WF) :
    parseRow (renderRow row) = .ok row := by
  have hclean : cleanField row.form = true ∧ cleanField row.lemma.render = true ∧
      cleanField row.upos.render = true ∧ cleanField row.xpos.render = true ∧
      cleanField row.feats.render = true ∧ cleanField row.deprel.render = true ∧
      cleanField row.deps.render = true ∧ cleanField row.misc.render = true := by
    have h := wf
    rw [CoNLLURow.WF, CoNLLURow.wf] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
      h.1.2, h.2⟩
  obtain ⟨hform, hlemma, hupos, hxpos, hfeats, hdeprel, hdeps, hmisc⟩ := hclean
  have hsplit : splitFields (renderRow row) =
      [row.id.render, row.form, row.lemma.render, row.upos.render, row.xpos.render,
        row.feats.render, renderHead row.head, row.deprel.render, row.deps.render,
        row.misc.render] := by
    apply splitFields_joinFields
    · intro field mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact row.id.render_tab_free
      · exact tab_free_of_cleanField hform
      · exact tab_free_of_cleanField hlemma
      · exact tab_free_of_cleanField hupos
      · exact tab_free_of_cleanField hxpos
      · exact tab_free_of_cleanField hfeats
      · exact renderHead_tab_free row.head
      · exact tab_free_of_cleanField hdeprel
      · exact tab_free_of_cleanField hdeps
      · exact tab_free_of_cleanField hmisc
    · simp
  simp only [parseRow, hsplit, CoNLLUId.parse_render, parseHead_renderHead,
    OptionalField.parse_render]

/-! ### Sentences -/

/-- Drop one trailing carriage return, so CRLF input parses like LF input. Rendering always
emits bare LF, so this leniency does not affect the round trip. -/
def stripCarriageReturn (line : String) : String :=
  if line.endsWith "\r" then (line.dropEnd 1).toString else line

/-- Parse a CoNLL-U document into sentences in a single pass over its lines. Blank lines
separate sentences, `#`-prefixed comment lines are skipped, and every other line must be a
valid token line. Total; the first bad line aborts with its 1-based line number. Empty
sentence blocks (e.g. consecutive blank lines or comment-only blocks) are dropped. -/
def parseSentences (input : String) : Except String (Array (Array CoNLLURow)) := do
  let mut sentences : Array (Array CoNLLURow) := #[]
  let mut current : Array CoNLLURow := #[]
  let mut lineNumber : Nat := 0
  for rawLine in input.splitOn "\n" do
    lineNumber := lineNumber + 1
    let line := stripCarriageReturn rawLine
    if line.isEmpty then
      unless current.isEmpty do
        sentences := sentences.push current
        current := #[]
    else if line.startsWith "#" then
      pure ()
    else
      match parseRow line with
      | .ok row => current := current.push row
      | .error message => throw s!"line {lineNumber}: {message}"
  unless current.isEmpty do
    sentences := sentences.push current
  return sentences

/-- Render sentences as a CoNLL-U document: each row on its own LF-terminated line, and a blank
line after every sentence (including the last, as the format requires). Comments are not
represented at this layer, so none are emitted. Right inverse of `parseSentences` on arrays of
nonempty sentences of `CoNLLURow.WF` rows (exercised by `native_decide` tests). -/
def renderSentences (sentences : Array (Array CoNLLURow)) : String :=
  sentences.foldl (init := "") fun output sentence ↦
    sentence.foldl (init := output) (fun output row ↦ output ++ renderRow row ++ "\n") ++ "\n"

end Nlp.IO
