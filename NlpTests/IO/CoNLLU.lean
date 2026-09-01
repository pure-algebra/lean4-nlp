import Nlp.IO.CoNLLU

/-!
# Tests for the CoNLL-U reader

`native_decide` round trips on authored synthetic sentences, field-count error cases,
multiword-token and empty-node IDs, and direct uses of the proved round-trip theorems.
-/

namespace NlpTests.IO.CoNLLU

open Nlp.IO

/-- Project an `Except String` result to its error message, if any. -/
def errorOf : Except String α → Option String
  | .error message => some message
  | .ok _ => none

/-! ### ID sub-parser: the three shapes, canonicalization, and rejections -/

example : (CoNLLUId.parse "7").toOption = some (.word 7) := by native_decide

example : (CoNLLUId.parse "29-30").toOption = some (.range 29 30) := by native_decide

example : (CoNLLUId.parse "8.1").toOption = some (.emptyNode 8 1) := by native_decide

example : (CoNLLUId.parse "0.1").toOption = some (.emptyNode 0 1) := by native_decide

/- Leading zeros parse (and canonicalize); rendering is always canonical. -/
example : (CoNLLUId.parse "07").toOption = some (.word 7) := by native_decide

example : CoNLLUId.render (.word 7) = "7" := by native_decide

example : CoNLLUId.render (.range 29 30) = "29-30" := by native_decide

example : CoNLLUId.render (.emptyNode 8 1) = "8.1" := by native_decide

/- Malformed IDs, including the `_` digit-separator hazard of `String.toNat?`. -/
example : (CoNLLUId.parse "").toOption = none := by native_decide

example : (CoNLLUId.parse "3-").toOption = none := by native_decide

example : (CoNLLUId.parse "-4").toOption = none := by native_decide

example : (CoNLLUId.parse "3-4-5").toOption = none := by native_decide

example : (CoNLLUId.parse "3.4.5").toOption = none := by native_decide

example : (CoNLLUId.parse "3.x").toOption = none := by native_decide

example : (CoNLLUId.parse "abc").toOption = none := by native_decide

example : (CoNLLUId.parse "1_0").toOption = none := by native_decide

/- The proved ID round trip, used as a theorem. -/
example (id : CoNLLUId) : CoNLLUId.parse id.render = .ok id := CoNLLUId.parse_render id

/-! ### Rows: multiword tokens, empty nodes, and the proved row round trip -/

/-- The multiword-token line `29-30 didn't` from UD English-EWT dev (see `sample` below). -/
def mwtRow : CoNLLURow where
  id := .range 29 30
  form := "didn't"
  lemma := .missing
  upos := .missing
  xpos := .missing
  feats := .missing
  head := none
  deprel := .missing
  deps := .missing
  misc := .present "SpaceAfter=No" (by decide)

example : mwtRow.WF := by native_decide

example : (parseRow "29-30\tdidn't\t_\t_\t_\t_\t_\t_\t_\tSpaceAfter=No").toOption
    = some mwtRow := by native_decide

example : renderRow mwtRow = "29-30\tdidn't\t_\t_\t_\t_\t_\t_\t_\tSpaceAfter=No" := by native_decide

/- The row round trip via the theorem, with the well-formedness side condition discharged by
kernel computation. -/
example : parseRow (renderRow mwtRow) = .ok mwtRow := parseRow_renderRow mwtRow (by native_decide)

example (row : CoNLLURow) (wf : row.WF) : parseRow (renderRow row) = .ok row :=
  parseRow_renderRow row wf

/-- An empty-node line in the style of EWT's enhanced graphs: HEAD and DEPREL are `_`,
DEPS carries the enhanced relation. -/
def emptyNodeRow : CoNLLURow where
  id := .emptyNode 3 1
  form := "likes"
  lemma := .present "like" (by decide)
  upos := .present "VERB" (by decide)
  xpos := .present "VBZ" (by decide)
  feats := .missing
  head := none
  deprel := .missing
  deps := .present "2:conj" (by decide)
  misc := .present "CopyOf=2" (by decide)

example : (parseRow "3.1\tlikes\tlike\tVERB\tVBZ\t_\t_\t_\t2:conj\tCopyOf=2").toOption
    = some emptyNodeRow := by native_decide

example : parseRow (renderRow emptyNodeRow) = .ok emptyNodeRow :=
  parseRow_renderRow emptyNodeRow (by native_decide)

/- HEAD is parsed: `0` is the root, `_` is missing. -/
example : (parseRow "1\ta\ta\tX\tX\t_\t0\troot\t_\t_").toOption.map (·.head)
    = some (some 0) := by native_decide

/- Field-count errors are descriptive: 9 and 11 fields. -/
example : errorOf (parseRow "1\tb\tc\td\te\tf\tg\th\ti")
    = some "expected 10 tab-separated fields, found 9" := by native_decide

example : errorOf (parseRow "1\tb\tc\td\te\tf\tg\th\ti\tj\tk")
    = some "expected 10 tab-separated fields, found 11" := by native_decide

/- Malformed ID and HEAD fields are rejected with their own messages. -/
example : errorOf (parseRow "x\tb\tc\td\te\tf\tg\th\ti\tj") = some "malformed word ID `x`" := by
  native_decide

example : errorOf (parseRow "1\tb\tc\td\te\tf\tg\th\ti\tj")
    = some "malformed HEAD `g`: expected `_` or a decimal index" := by native_decide

/- Well-formedness rejects embedded delimiters and empty fields. -/
example : ({ mwtRow with form := "with\ttab" } : CoNLLURow).wf = false := by native_decide

example : ({ mwtRow with form := "with\nnewline" } : CoNLLURow).wf = false := by native_decide

example : ({ mwtRow with upos := .present "" (by decide) } : CoNLLURow).wf = false := by
  native_decide

/-! ### Sentences

Two small, project-authored sentences exercise comments, sentence boundaries, morphological
features, enhanced dependencies, and the multiword-token range `2-3 can't`.
-/

/-- Authored two-sentence CoNLL-U regression sample. -/
def sample : String := String.intercalate "\n" [
  "# sent_id = synthetic-1",
  "# text = Cats purr.",
  "1\tCats\tcat\tNOUN\tNNS\tNumber=Plur\t2\tnsubj\t2:nsubj\t_",
  "2\tpurr\tpurr\tVERB\tVBP\tMood=Ind|Tense=Pres\t0\troot\t0:root\tSpaceAfter=No",
  "3\t.\t.\tPUNCT\t.\t_\t2\tpunct\t2:punct\t_",
  "",
  "# sent_id = synthetic-2",
  "# text = I can't wait.",
  "1\tI\tI\tPRON\tPRP\tCase=Nom|Number=Sing|Person=1\t4\tnsubj\t4:nsubj\t_",
  "2-3\tcan't\t_\t_\t_\t_\t_\t_\t_\t_",
  "2\tca\tcan\tAUX\tMD\tVerbForm=Fin\t4\taux\t4:aux\t_",
  "3\tn't\tnot\tPART\tRB\tPolarity=Neg\t4\tadvmod\t4:advmod\t_",
  "4\twait\twait\tVERB\tVB\tVerbForm=Inf\t0\troot\t0:root\tSpaceAfter=No",
  "5\t.\t.\tPUNCT\t.\t_\t4\tpunct\t4:punct\t_",
  ""]

/-- A synthetic minimal sentence with an empty node, exercising `parseSentences` on the
enhanced-graph line shape. -/
def emptyNodeSample : String := String.intercalate "\n" [
  "# a minimal synthetic enhanced-graph fragment",
  "1\tSue\tSue\tPROPN\tNNP\t_\t2\tnsubj\t2:nsubj\t_",
  "2\tlikes\tlike\tVERB\tVBZ\t_\t0\troot\t0:root\t_",
  "3\tcoffee\tcoffee\tNOUN\tNN\t_\t2\tobj\t2:obj\t_",
  "3.1\tlikes\tlike\tVERB\tVBZ\t_\t_\t_\t2:conj\tCopyOf=2",
  ""]

/- Comments are skipped and blank lines separate two sentences of 3 and 6 rows. -/
example : (parseSentences sample).toOption.map (·.map (·.size)) = some #[3, 6] := by
  native_decide

/- The multiword-token and word IDs land where they should inside the parsed sample. -/
example : (parseSentences sample).toOption.map (fun ss ↦ ss[1]![1]!.id)
    = some (.range 2 3) := by native_decide

example : (parseSentences sample).toOption.map (fun ss ↦ ss[0]![2]!.id)
    = some (.word 3) := by native_decide

/- Every row parsed from the sample is well-formed. -/
example : (parseSentences sample).toOption.map (·.all (·.all (·.wf))) = some true := by
  native_decide

/-- `true` iff `input` parses and its canonical re-rendering parses back to the same
sentences (comments are dropped by design, so this is the honest sentence-level round trip). -/
def roundTrips (input : String) : Bool :=
  match parseSentences input with
  | .ok sentences =>
    match parseSentences (renderSentences sentences) with
    | .ok reparsed => decide (reparsed = sentences)
    | .error _ => false
  | .error _ => false

example : roundTrips sample = true := by native_decide

example : roundTrips emptyNodeSample = true := by native_decide

/- The empty node parses structurally faithfully inside a sentence. -/
example : (parseSentences emptyNodeSample).toOption.map (fun ss ↦ ss[0]![3]!.id)
    = some (.emptyNode 3 1) := by native_decide

/- CRLF input parses like LF input (rendering always emits bare LF). -/
example : (parseSentences "# c\r\n1\ta\ta\tX\tX\t_\t0\troot\t_\t_\r\n\r\n").toOption.map
    (·.map (·.size)) = some #[1] := by native_decide

/- Sentence-level errors carry 1-based line numbers. -/
example : errorOf (parseSentences "# ok\n1\tonly\n")
    = some "line 2: expected 10 tab-separated fields, found 2" := by native_decide

/- Degenerate inputs: no sentences. -/
example : (parseSentences "").toOption = some #[] := by native_decide

example : (parseSentences "\n\n# only a comment\n\n").toOption = some #[] := by native_decide

example : renderSentences #[] = "" := by native_decide

end NlpTests.IO.CoNLLU
