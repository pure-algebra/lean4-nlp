import Init.Data.String.Basic
import Nlp.Core.Data.Dependency
import Nlp.Core.Data.Span
import Nlp.Core.Extra
import Nlp.Core.Layer

/-!
# Columnar annotated documents

`Doc ls` stores core annotations in parallel arrays while `ls` records which layers have run.
The index is phantom and the gated accessors erase their proof arguments. `Doc.WF` is checked at
input boundaries; it is intentionally not stored as a proof field on every document value.
-/

namespace Nlp

/-- A document with the completed annotation layers `ls`.

Core token annotations use a struct-of-arrays representation. The raw columns support efficient
functional record updates inside annotators; consumers should prefer the layer-gated accessors.
-/
structure Doc (ls : Layers) where
  text : String
  spans : Array Span := #[]
  forms : Array String := #[]
  sentEnd : Array Nat := #[]
  pos : Array String := #[]
  lemma : Array String := #[]
  ner : Array String := #[]
  head : Array Nat := #[]
  deprel : Array String := #[]
  extra : Extra := ∅

namespace Doc

/-- The number of token positions in a document. -/
@[inline] def size (doc : Doc ls) : Nat := doc.forms.size

/-- Column-size invariants for the layers represented by a document.

Token forms and spans always align. A completed token-level layer has exactly one entry per token;
dependency annotation has both a head and a relation entry per token. Sentence and parse layers
have sentence-level cardinalities and are intentionally outside this first predicate.
-/
def WF {ls : Layers} (doc : Doc ls) : Prop :=
  doc.spans.size = doc.size ∧
    (Layer.pos ∈ ls → doc.pos.size = doc.size) ∧
    (Layer.lemma ∈ ls → doc.lemma.size = doc.size) ∧
    (Layer.ner ∈ ls → doc.ner.size = doc.size) ∧
    (Layer.dep ∈ ls → doc.head.size = doc.size ∧ doc.deprel.size = doc.size)

instance instDecidableWF {ls : Layers} (doc : Doc ls) : Decidable doc.WF := by
  unfold WF
  infer_instance

/-- A token span is nonempty and names complete UTF-8 code points inside `text`. -/
def SpanValid (text : String) (span : Span) : Prop :=
  span.b < span.e ∧ span.e ≤ text.utf8ByteSize ∧
    (String.Pos.Raw.mk span.b).IsValid text ∧
    (String.Pos.Raw.mk span.e).IsValid text

instance instDecidableSpanValid (text : String) (span : Span) :
    Decidable (SpanValid text span) := by
  unfold SpanValid
  infer_instance

/-- Adjacent token spans occur in source order without overlap. -/
def spansOrdered : List Span → Bool
  | [] | [_] => true
  | left :: right :: rest => left.e ≤ right.b && spansOrdered (right :: rest)
termination_by spans => spans.length

/-- Adjacent sentence ends increase strictly. -/
def strictlyIncreasing : List Nat → Bool
  | [] | [_] => true
  | left :: right :: rest => left < right && strictlyIncreasing (right :: rest)
termination_by ends => ends.length

@[inline] private def spansOrderedArray (spans : Array Span) : Bool :=
  Nat.allLTTR (spans.size - 1) fun index beforeLast ↦
    decide ((spans[index]'(by omega)).e ≤ (spans[index + 1]'(by omega)).b)

@[inline] private def strictlyIncreasingArray (ends : Array Nat) : Bool :=
  Nat.allLTTR (ends.size - 1) fun index beforeLast ↦
    decide (ends[index]'(by omega) < ends[index + 1]'(by omega))

private theorem spansOrdered_eq_true_iff_getElem (spans : List Span) :
    spansOrdered spans = true ↔
      ∀ index (next : index + 1 < spans.length),
        (spans[index]'(by omega)).e ≤ (spans[index + 1]'next).b := by
  induction spans with
  | nil => simp [spansOrdered]
  | cons left rest ih =>
    cases rest with
    | nil => simp [spansOrdered]
    | cons right tail =>
      rw [spansOrdered, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨first, later⟩ index next
        cases index with
        | zero => simpa using first
        | succ index =>
          have laterBound : index + 1 < (right :: tail).length := by
            simp only [List.length_cons] at next ⊢
            omega
          simpa using later index laterBound
      · intro ordered
        constructor
        · simpa using ordered 0 (by simp)
        · intro index next
          have orderedBound : (index + 1) + 1 < (left :: right :: tail).length := by
            simp only [List.length_cons] at next ⊢
            omega
          simpa using ordered (index + 1) orderedBound

private theorem strictlyIncreasing_eq_true_iff_getElem (ends : List Nat) :
    strictlyIncreasing ends = true ↔
      ∀ index (next : index + 1 < ends.length),
        ends[index]'(by omega) < ends[index + 1]'next := by
  induction ends with
  | nil => simp [strictlyIncreasing]
  | cons left rest ih =>
    cases rest with
    | nil => simp [strictlyIncreasing]
    | cons right tail =>
      rw [strictlyIncreasing, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨first, later⟩ index next
        cases index with
        | zero => simpa using first
        | succ index =>
          have laterBound : index + 1 < (right :: tail).length := by
            simp only [List.length_cons] at next ⊢
            omega
          simpa using later index laterBound
      · intro ordered
        constructor
        · simpa using ordered 0 (by simp)
        · intro index next
          have orderedBound : (index + 1) + 1 < (left :: right :: tail).length := by
            simp only [List.length_cons] at next ⊢
            omega
          simpa using ordered (index + 1) orderedBound

private theorem spansOrderedArray_eq (spans : Array Span) :
    spansOrderedArray spans = spansOrdered spans.toList := by
  rw [Bool.eq_iff_iff, spansOrdered_eq_true_iff_getElem, spansOrderedArray,
    Nat.allLTTR_eq_true]
  simp only [Array.length_toList, Array.getElem_toList, decide_eq_true_eq]
  constructor <;> intro ordered index bound
  · exact ordered index (by omega)
  · exact ordered index (by omega)

private theorem strictlyIncreasingArray_eq (ends : Array Nat) :
    strictlyIncreasingArray ends = strictlyIncreasing ends.toList := by
  rw [Bool.eq_iff_iff, strictlyIncreasing_eq_true_iff_getElem,
    strictlyIncreasingArray, Nat.allLTTR_eq_true]
  simp only [Array.length_toList, Array.getElem_toList, decide_eq_true_eq]
  constructor <;> intro ordered index bound
  · exact ordered index (by omega)
  · exact ordered index (by omega)

/-- Semantic invariants for the token columns of a document. -/
def TokenWF {ls : Layers} (doc : Doc ls) : Prop :=
  doc.spans.size = doc.size ∧
    (∀ form ∈ doc.forms, form ≠ "") ∧
    (∀ span ∈ doc.spans, SpanValid doc.text span) ∧
    spansOrdered doc.spans.toList = true

instance instDecidableTokenWF {ls : Layers} (doc : Doc ls) : Decidable doc.TokenWF := by
  unfold TokenWF
  rw [← spansOrderedArray_eq doc.spans]
  infer_instance

/-- Semantic invariants for sentence ends, using `#[]` for an empty token sequence. -/
def SentenceWF {ls : Layers} (doc : Doc ls) : Prop :=
  (∀ ending ∈ doc.sentEnd, 0 < ending ∧ ending ≤ doc.size) ∧
    strictlyIncreasing doc.sentEnd.toList = true ∧
    if doc.size = 0 then doc.sentEnd = #[] else doc.sentEnd.back? = some doc.size

instance instDecidableSentenceWF {ls : Layers} (doc : Doc ls) :
    Decidable doc.SentenceWF := by
  unfold SentenceWF
  rw [← strictlyIncreasingArray_eq doc.sentEnd]
  infer_instance

/--
Dependency-tree invariants under the document's sentence convention.

Heads are sentence-local. Advertised sentence ends split the flattened columns into separately
rooted trees; without a sentence layer, the whole document is one tree.
-/
def DependencyWF {ls : Layers} (doc : Doc ls) : Prop :=
  if Layer.sents ∈ ls then
    Dependency.DocumentTreeWF doc.head doc.sentEnd
  else
    Dependency.SentenceTreeWF doc.head

instance instDecidableDependencyWF {ls : Layers} (doc : Doc ls) :
    Decidable doc.DependencyWF := by
  unfold DependencyWF
  infer_instance

/-- Full semantic boundary invariant layered on top of the compatible column-size invariant. -/
def SemanticWF {ls : Layers} (doc : Doc ls) : Prop :=
  doc.WF ∧
    (Layer.tokens ∈ ls → doc.TokenWF) ∧
    (Layer.sents ∈ ls → Layer.tokens ∈ ls ∧ doc.SentenceWF) ∧
    (Layer.dep ∈ ls → Layer.tokens ∈ ls ∧ doc.DependencyWF)

instance instDecidableSemanticWF {ls : Layers} (doc : Doc ls) :
    Decidable doc.SemanticWF := by
  unfold SemanticWF
  infer_instance

/-- Semantic well-formedness includes compatible annotation-column sizes. -/
theorem semanticWF_wf {ls : Layers} {doc : Doc ls} (semantic : doc.SemanticWF) : doc.WF :=
  semantic.1

/-- Extract token-column invariants when the document advertises a token layer. -/
theorem semanticWF_token {ls : Layers} {doc : Doc ls} (semantic : doc.SemanticWF)
    (tokens : Layer.tokens ∈ ls) : doc.TokenWF :=
  semantic.2.1 tokens

/-- A semantically valid sentence layer always carries its token layer. -/
theorem semanticWF_tokens_of_sents {ls : Layers} {doc : Doc ls}
    (semantic : doc.SemanticWF) (sentences : Layer.sents ∈ ls) : Layer.tokens ∈ ls :=
  (semantic.2.2.1 sentences).1

/-- Extract sentence-boundary invariants from a semantically valid sentence document. -/
theorem semanticWF_sentence {ls : Layers} {doc : Doc ls} (semantic : doc.SemanticWF)
    (sentences : Layer.sents ∈ ls) : doc.SentenceWF :=
  (semantic.2.2.1 sentences).2

/-- A semantically valid dependency layer always carries its token layer. -/
theorem semanticWF_tokens_of_dep {ls : Layers} {doc : Doc ls}
    (semantic : doc.SemanticWF) (dependency : Layer.dep ∈ ls) : Layer.tokens ∈ ls :=
  (semantic.2.2.2 dependency).1

/-- Extract the sentence-aware dependency-tree invariant. -/
theorem semanticWF_dependency {ls : Layers} {doc : Doc ls} (semantic : doc.SemanticWF)
    (dependency : Layer.dep ∈ ls) : doc.DependencyWF :=
  (semantic.2.2.2 dependency).2

/-- Every advertised token span is valid for the document's exact source string. -/
theorem semanticWF_span {ls : Layers} {doc : Doc ls} (semantic : doc.SemanticWF)
    (tokens : Layer.tokens ∈ ls) {span : Span} (present : span ∈ doc.spans) :
    SpanValid doc.text span :=
  (semanticWF_token semantic tokens).2.2.1 span present

/-- Counts reported when a document fails `Doc.WF`. -/
structure ColumnSizes where
  forms : Nat
  spans : Nat
  pos : Nat
  lemma : Nat
  ner : Nat
  head : Nat
  deprel : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A document failed boundary validation. -/
inductive ValidationError where
  | invalidColumnSizes (sizes : ColumnSizes)
  deriving Repr, DecidableEq, Inhabited

/-- The endpoint of a token span that is not aligned to a UTF-8 code-point boundary. -/
inductive SpanEndpoint where
  | begin
  | end
  deriving Repr, DecidableEq, Inhabited

/-- Actionable failures produced by the stronger semantic document boundary. -/
inductive SemanticError where
  | structural (cause : ValidationError)
  | sentenceLayerRequiresTokens
  | dependencyLayerRequiresTokens
  | emptyTokenForm (index : Nat)
  | emptyTokenSpan (index : Nat) (span : Span)
  | reversedTokenSpan (index : Nat) (span : Span)
  | tokenSpanOutOfBounds (index : Nat) (span : Span) (textBytes : Nat)
  | tokenSpanNotUtf8Boundary (index : Nat) (endpoint : SpanEndpoint) (offset : Nat)
  | overlappingTokenSpans (leftIndex : Nat) (left right : Span)
  | sentenceEndsForEmptyTokens (ends : Array Nat)
  | missingSentenceEnd (tokens : Nat)
  | emptySentence (index : Nat)
  | sentenceEndOutOfBounds (index ending tokens : Nat)
  | nonIncreasingSentenceEnds (leftIndex left right : Nat)
  | finalSentenceEnd (expected found : Nat)
  | invalidDependencyTree (cause : Dependency.TreeError)
  | invalidDependencyDocument (cause : Dependency.DocumentTreeError)
  | inconsistentSemanticState (textBytes tokens sentenceEnds : Nat)
  deriving Repr, DecidableEq, Inhabited

@[inline] private def columnSizes (doc : Doc ls) : ColumnSizes where
  forms := doc.forms.size
  spans := doc.spans.size
  pos := doc.pos.size
  lemma := doc.lemma.size
  ner := doc.ner.size
  head := doc.head.size
  deprel := doc.deprel.size

/-- Validate a document at an input or model boundary without changing its runtime shape. -/
def checked (doc : Doc ls) : Except ValidationError (Doc ls) :=
  if doc.WF then .ok doc else .error (.invalidColumnSizes (columnSizes doc))

theorem checked_eq_ok_iff (doc : Doc ls) : checked doc = .ok doc ↔ doc.WF := by
  by_cases wellFormed : doc.WF <;> simp [checked, wellFormed]

private structure TokenErrorScan where
  emptyForm : Option Nat
  emptySpan : Option (Nat × Span)
  reversedSpan : Option (Nat × Span)
  outOfBounds : Option (Nat × Span)
  invalidBegin : Option (Nat × Span)
  invalidEnd : Option (Nat × Span)
  overlap : Option (Nat × Span × Span)

private def scanTokenErrors (doc : Doc ls) : TokenErrorScan := Id.run do
  let textBytes := doc.text.utf8ByteSize
  let mut emptyForm : Option Nat := none
  let mut emptySpan : Option (Nat × Span) := none
  let mut reversedSpan : Option (Nat × Span) := none
  let mut outOfBounds : Option (Nat × Span) := none
  let mut invalidBegin : Option (Nat × Span) := none
  let mut invalidEnd : Option (Nat × Span) := none
  let mut overlap : Option (Nat × Span × Span) := none
  let mut previous : Option (Nat × Span) := none
  for index in [0:doc.spans.size] do
    let span := doc.spans[index]!
    if emptyForm.isNone && (doc.forms[index]!).isEmpty then
      emptyForm := some index
    if span.b = span.e then
      if emptySpan.isNone then
        emptySpan := some (index, span)
    else if span.e < span.b then
      if reversedSpan.isNone then
        reversedSpan := some (index, span)
    else if textBytes < span.e then
      if outOfBounds.isNone then
        outOfBounds := some (index, span)
    else
      if invalidBegin.isNone && !(String.Pos.Raw.isValid doc.text (.mk span.b)) then
        invalidBegin := some (index, span)
      if invalidEnd.isNone && !(String.Pos.Raw.isValid doc.text (.mk span.e)) then
        invalidEnd := some (index, span)
    if overlap.isNone then
      match previous with
      | some (leftIndex, left) =>
        if !(left.e ≤ span.b) then
          overlap := some (leftIndex, left, span)
      | none => pure ()
    previous := some (index, span)
  return TokenErrorScan.mk emptyForm emptySpan reversedSpan outOfBounds invalidBegin invalidEnd
    overlap

private structure SentenceErrorScan where
  empty : Option Nat
  outOfBounds : Option (Nat × Nat)
  nonIncreasing : Option (Nat × Nat × Nat)

private def scanSentenceErrors (ends : Array Nat) (tokens : Nat) : SentenceErrorScan := Id.run do
  let mut empty : Option Nat := none
  let mut outOfBounds : Option (Nat × Nat) := none
  let mut nonIncreasing : Option (Nat × Nat × Nat) := none
  let mut previous : Option (Nat × Nat) := none
  for index in [0:ends.size] do
    let ending := ends[index]!
    if empty.isNone && ending = 0 then
      empty := some index
    if outOfBounds.isNone && tokens < ending then
      outOfBounds := some (index, ending)
    if nonIncreasing.isNone then
      match previous with
      | some (leftIndex, left) =>
        if !(left < ending) then
          nonIncreasing := some (leftIndex, left, ending)
      | none => pure ()
    previous := some (index, ending)
  return SentenceErrorScan.mk empty outOfBounds nonIncreasing

private def tokenError? (doc : Doc ls) : Option SemanticError :=
  let errors := scanTokenErrors doc
  match errors.emptyForm with
  | some index => some (.emptyTokenForm index)
  | none => match errors.emptySpan with
    | some (index, span) => some (.emptyTokenSpan index span)
    | none => match errors.reversedSpan with
      | some (index, span) => some (.reversedTokenSpan index span)
      | none => match errors.outOfBounds with
        | some (index, span) =>
          some (.tokenSpanOutOfBounds index span doc.text.utf8ByteSize)
        | none => match errors.invalidBegin with
          | some (index, span) => some (.tokenSpanNotUtf8Boundary index .begin span.b)
          | none => match errors.invalidEnd with
            | some (index, span) => some (.tokenSpanNotUtf8Boundary index .end span.e)
            | none => match errors.overlap with
              | some (index, left, right) => some (.overlappingTokenSpans index left right)
              | none => none

private def sentenceError? (doc : Doc ls) : Option SemanticError :=
  if doc.size = 0 then
    if doc.sentEnd.isEmpty then none else some (.sentenceEndsForEmptyTokens doc.sentEnd)
  else if doc.sentEnd.isEmpty then
    some (.missingSentenceEnd doc.size)
  else
    let errors := scanSentenceErrors doc.sentEnd doc.size
    match errors.empty with
    | some index => some (.emptySentence index)
    | none => match errors.outOfBounds with
      | some (index, ending) => some (.sentenceEndOutOfBounds index ending doc.size)
      | none => match errors.nonIncreasing with
        | some (index, left, right) => some (.nonIncreasingSentenceEnds index left right)
        | none =>
          match doc.sentEnd.back? with
          | some ending =>
            if ending = doc.size then none else some (.finalSentenceEnd doc.size ending)
          | none => some (.missingSentenceEnd doc.size)

private def dependencyError? (doc : Doc ls) : Option SemanticError :=
  if Layer.sents ∈ ls then
    match Dependency.checkDocumentTrees doc.head doc.sentEnd with
    | .ok () => none
    | .error cause => some (.invalidDependencyDocument cause)
  else
    match Dependency.checkSentenceTree doc.head with
    | .ok () => none
    | .error cause => some (.invalidDependencyTree cause)

private def semanticError (doc : Doc ls) : SemanticError :=
  match checked doc with
  | .error cause => .structural cause
  | .ok _ =>
    if Layer.sents ∈ ls ∧ Layer.tokens ∉ ls then
      .sentenceLayerRequiresTokens
    else if Layer.dep ∈ ls ∧ Layer.tokens ∉ ls then
      .dependencyLayerRequiresTokens
    else
      let tokenCause := if Layer.tokens ∈ ls then tokenError? doc else none
      match tokenCause with
      | some cause => cause
      | none =>
        let sentenceCause := if Layer.sents ∈ ls then sentenceError? doc else none
        match sentenceCause with
        | some cause => cause
        | none =>
          let dependencyCause := if Layer.dep ∈ ls then dependencyError? doc else none
          dependencyCause.getD
            (.inconsistentSemanticState doc.text.utf8ByteSize doc.size doc.sentEnd.size)

/-- Validate all layer, token-span, and sentence-boundary semantics at an external boundary. -/
def checkedSemantic (doc : Doc ls) : Except SemanticError (Doc ls) :=
  if doc.SemanticWF then .ok doc else .error (semanticError doc)

/-- Semantic checking succeeds exactly for semantically well-formed documents. -/
theorem checkedSemantic_eq_ok_iff (doc : Doc ls) :
    checkedSemantic doc = .ok doc ↔ doc.SemanticWF := by
  by_cases wellFormed : doc.SemanticWF <;> simp [checkedSemantic, wellFormed]

/-- Safely recover a token's exact source slice from its validated UTF-8 byte span. -/
def originalAt? (doc : Doc ls) (i : Nat)
    (_needsTokens : Layer.tokens ∈ ls := by decide) : Option String := do
  let span ← doc.spans[i]?
  if valid : SpanValid doc.text span then
    let start : doc.text.Pos := ⟨.mk span.b, valid.2.2.1⟩
    let stop : doc.text.Pos := ⟨.mk span.e, valid.2.2.2⟩
    some (doc.text.extract start stop)
  else
    none

/-- A recovered original token always came from a valid source span. -/
theorem spanValid_of_originalAt?_eq_some (doc : Doc ls) (i : Nat)
    (needsTokens : Layer.tokens ∈ ls) {original : String}
    (found : originalAt? doc i needsTokens = some original) :
    ∃ span, doc.spans[i]? = some span ∧ SpanValid doc.text span := by
  cases spanFound : doc.spans[i]? with
  | none => simp [originalAt?, spanFound] at found
  | some span =>
    by_cases valid : SpanValid doc.text span
    · exact ⟨span, rfl, valid⟩
    · simp [originalAt?, spanFound, valid] at found

/-- Construct and validate the token layer produced by a tokenizer. -/
def ofTokens (text : String) (spans : Array Span) (forms : Array String) :
    Except ValidationError (Doc [.tokens]) :=
  checked { text, spans, forms }

/-- An empty, well-formed document before tokenization. -/
def empty (text : String) : Doc [] := { text }

theorem empty_wf (text : String) : (empty text).WF := by simp [empty, WF, size]

/-- Read a token form only from a document whose token layer is present. -/
@[inline] def formAt (doc : Doc ls) (i : Nat)
    (_needsTokens : Layer.tokens ∈ ls := by decide) : String :=
  doc.forms[i]!

/-- Read a token span only from a document whose token layer is present. -/
@[inline] def spanAt (doc : Doc ls) (i : Nat)
    (_needsTokens : Layer.tokens ∈ ls := by decide) : Span :=
  doc.spans[i]!

/-- Read a POS tag only from a document whose POS layer is present. -/
@[inline] def posAt (doc : Doc ls) (i : Nat)
    (_needsPos : Layer.pos ∈ ls := by decide) : String :=
  doc.pos[i]!

/-- Read a lemma only from a document whose lemma layer is present. -/
@[inline] def lemmaAt (doc : Doc ls) (i : Nat)
    (_needsLemma : Layer.lemma ∈ ls := by decide) : String :=
  doc.lemma[i]!

/-- Read an entity tag only from a document whose NER layer is present. -/
@[inline] def nerAt (doc : Doc ls) (i : Nat)
    (_needsNer : Layer.ner ∈ ls := by decide) : String :=
  doc.ner[i]!

/-- Read a dependency head only from a document whose dependency layer is present. -/
@[inline] def headAt (doc : Doc ls) (i : Nat)
    (_needsDep : Layer.dep ∈ ls := by decide) : Nat :=
  doc.head[i]!

/-- Read a dependency relation only from a document whose dependency layer is present. -/
@[inline] def deprelAt (doc : Doc ls) (i : Nat)
    (_needsDep : Layer.dep ∈ ls := by decide) : String :=
  doc.deprel[i]!

end Doc

end Nlp
