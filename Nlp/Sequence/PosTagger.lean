import Nlp.Core.Data.Interner
import Nlp.Sequence.HmmLemmas

/-!
# Named part-of-speech tagging over numeric hidden Markov models

`Hmm` deliberately keeps its hot path numeric. `PosTagger` is the validated pure model boundary
that gives those word and tag identifiers stable string names. Unknown forms receive one reserved
identifier outside the compiled vocabulary, so they always use the HMM's unknown-word costs.
-/

namespace Nlp.Sequence

/-- A validated named view of a numeric HMM tagger. -/
structure PosTagger where
  private mk ::
  /-- The validated numeric decoding kernel. -/
  hmm : Hmm
  /-- Exact, case-sensitive word names indexed by their numeric observations. -/
  words : Interner
  /-- Output tag names indexed by the HMM's dense states. -/
  tagNames : Array String
  /-- A reserved observation identifier outside `words`. -/
  oov : Tok
  /-- The HMM has at least one state, making named decoding length preserving. -/
  positiveTags : 0 < hmm.nTags
  /-- The HMM's dense arrays agree with its declared tag count. -/
  wellFormedHmm : hmm.WF
  /-- Every dense HMM state has exactly one output name. -/
  tagCount : tagNames.size = hmm.nTags
  /-- Dense tags fit the 32-bit half of a packed emission key. -/
  tagCapacity : tagNames.size ≤ UInt32.size

namespace PosTagger

/-- Why ordered names and a numeric HMM could not form a production tagger model. -/
inductive CompileError where
  | zeroTags
  | wordCapacity (count : Nat)
  | tagCapacity (count : Nat)
  | invalidDimensions (nTags start transitions unknown : Nat)
  | invalidTagCount (expected found : Nat)
  | emptyWordName (index : Nat)
  | duplicateWordName (first duplicate : Nat) (name : String)
  | emptyTagName (index : Nat)
  | duplicateTagName (first duplicate : Nat) (name : String)
  | invalidStartCost (index : Nat) (value : Float) (bits : UInt64)
  | invalidTransitionCost (index : Nat) (value : Float) (bits : UInt64)
  | invalidUnknownCost (index : Nat) (value : Float) (bits : UInt64)
  | invalidEmissionCost (key : UInt64) (value : Float) (bits : UInt64)
  | emissionTagOutOfRange (key : UInt64) (tag nTags : Nat)
  | emissionWordOutOfRange (key : UInt64) (word vocabulary : Nat)
  deriving Repr

/-- Which ordered namespace is being validated. -/
private inductive NameKind where
  | word
  | tag

/-- Report an empty ordered name in its source namespace. -/
private def emptyNameError : NameKind → Nat → CompileError
  | .word, index => .emptyWordName index
  | .tag, index => .emptyTagName index

/-- Report both stable positions of a duplicate ordered name. -/
private def duplicateNameError : NameKind → Nat → Nat → String → CompileError
  | .word, first, duplicate, name => .duplicateWordName first duplicate name
  | .tag, first, duplicate, name => .duplicateTagName first duplicate name

/-- Build the canonical dense interner represented by an ordered array of distinct names. -/
private def buildInterner (kind : NameKind) (names : Array String) :
    Except CompileError Interner := do
  let mut ids : Std.HashMap String UInt32 := Std.HashMap.emptyWithCapacity names.size
  for index in [0:names.size] do
    let name := names[index]!
    if name.isEmpty then
      throw <| emptyNameError kind index
    match ids.get? name with
    | some first => throw <| duplicateNameError kind first.toNat index name
    | none => ids := ids.insert name (UInt32.ofNat index)
  return { ids, names }

/-- IEEE-754 bits of the noncanonical negative-zero cost. -/
private def negativeZeroBits : UInt64 := 0x8000000000000000

/-- Canonical HMM costs are finite, nonnegative, and use positive zero. -/
@[inline] def isCanonicalCost (cost : Cost) : Bool :=
  let value := cost.toFloat
  value.isFinite && decide (0.0 ≤ value) && value.toBits != negativeZeroBits

/-- Validate one dense cost array while retaining the failing source position. -/
private def validateArrayCosts (costs : Array Cost)
    (error : Nat → Float → UInt64 → CompileError) : Except CompileError Unit := do
  for index in [0:costs.size] do
    let value := costs[index]!.toFloat
    unless isCanonicalCost costs[index]! do
      throw <| error index value value.toBits

/-- Recover the dense tag encoded in an HMM emission-table key. -/
@[inline] def emissionTag (key : UInt64) : Nat :=
  (key >>> 32).toNat

/-- Recover the word observation encoded in an HMM emission-table key. -/
@[inline] def emissionWord (key : UInt64) : Tok :=
  key.toUInt32

/-- Select the fixed tag, word, then cost failure for one sparse emission entry. -/
private def emissionError? (hmm : Hmm) (vocabulary : Nat) (key : UInt64)
    (cost : Cost) : Option CompileError :=
  let tag := emissionTag key
  let word := (emissionWord key).toNat
  if !(tag < hmm.nTags) then
    some (.emissionTagOutOfRange key tag hmm.nTags)
  else if !(word < vocabulary) then
    some (.emissionWordOutOfRange key word vocabulary)
  else if !isCanonicalCost cost then
    let value := cost.toFloat
    some (.invalidEmissionCost key value value.toBits)
  else
    none

/-- Validate sparse emissions deterministically without materializing or sorting the hash map. -/
private def validateEmissions (hmm : Hmm) (vocabulary : Nat) : Except CompileError Unit := do
  let mut first : Option (UInt64 × CompileError) := none
  for (key, cost) in hmm.emit do
    match emissionError? hmm vocabulary key cost with
    | none => pure ()
    | some cause =>
      match first with
      | none => first := some (key, cause)
      | some (priorKey, _) =>
        if key < priorKey then
          first := some (key, cause)
  match first with
  | some (_, cause) => throw cause
  | none => pure ()

/--
Validate ordered word and tag names around an existing numeric HMM.

`wordNames[i]` names observation `i`; `tagNames[i]` names state `i`. Both namespaces are exact and
case-sensitive. One additional `UInt32` value is reserved after the word vocabulary for OOV input.
-/
def compile (hmm : Hmm) (wordNames tagNames : Array String) :
    Except CompileError PosTagger :=
  if _wordCapacity : wordNames.size < UInt32.size then
    if tagCapacity : tagNames.size ≤ UInt32.size then
      if positiveTags : 0 < hmm.nTags then
        if wellFormedHmm :
            hmm.start.size = hmm.nTags ∧
              hmm.trans.size = hmm.nTags * hmm.nTags ∧ hmm.unk.size = hmm.nTags then
          if tagCount : tagNames.size = hmm.nTags then do
            let words ← buildInterner .word wordNames
            let _tags ← buildInterner .tag tagNames
            validateArrayCosts hmm.start .invalidStartCost
            validateArrayCosts hmm.trans .invalidTransitionCost
            validateArrayCosts hmm.unk .invalidUnknownCost
            validateEmissions hmm wordNames.size
            return {
              hmm
              words
              tagNames
              oov := UInt32.ofNat wordNames.size
              positiveTags
              wellFormedHmm
              tagCount
              tagCapacity
            }
          else
            .error <| .invalidTagCount hmm.nTags tagNames.size
        else
          .error <|
            .invalidDimensions hmm.nTags hmm.start.size hmm.trans.size hmm.unk.size
      else
        .error .zeroTags
    else
      .error <| .tagCapacity tagNames.size
  else
    .error <| .wordCapacity wordNames.size

/-- Preserve the exhausted namespace when adapting an interner failure. -/
private def internerCapacityError : NameKind → Interner.Error → CompileError
  | .word, .capacityExceeded limit => .wordCapacity limit
  | .tag, .capacityExceeded limit => .tagCapacity limit

/-- Intern one training name while retaining whether it was a word or tag. -/
private def internName (kind : NameKind) (interner : Interner) (name : String) :
    Except CompileError (Interner × UInt32) :=
  match interner.intern name with
  | .ok result => .ok result
  | .error cause => .error (internerCapacityError kind cause)

/--
Estimate and validate a named HMM from sentences of `(surface form, POS tag)` observations.

Distinct word and tag identifiers are allocated in first-occurrence order. Names and later lookup
remain exact and case-sensitive; `addK` has the same normalization policy as `Hmm.estimate`.
-/
def estimate (sentences : Array (Array (String × String))) (addK : Float := 1.0) :
    Except CompileError PosTagger := do
  let mut words := Interner.empty
  let mut tags := Interner.empty
  let mut encoded := Array.emptyWithCapacity sentences.size
  for sentence in sentences do
    let mut encodedSentence := Array.emptyWithCapacity sentence.size
    for (form, tagName) in sentence do
      let (nextWords, word) ← internName .word words form
      words := nextWords
      let (nextTags, tag) ← internName .tag tags tagName
      tags := nextTags
      encodedSentence := encodedSentence.push (word, tag.toNat)
    encoded := encoded.push encodedSentence
  compile (Hmm.estimate encoded tags.size addK) words.names tags.names

/-- Ordered word names retained by a validated tagger. -/
@[inline] def wordNames (tagger : PosTagger) : Array String :=
  tagger.words.names

/-- Encode one form exactly, using the reserved OOV observation when it was not compiled. -/
@[inline] def encode (tagger : PosTagger) (form : String) : Tok :=
  (tagger.words.lookup? form).getD tagger.oov

/-- Encode a column of forms with exact, case-sensitive lookup. -/
def encodeForms (tagger : PosTagger) (forms : Array String) : Array Tok :=
  forms.map tagger.encode

/-- Expose the numeric decoder result for named input forms. -/
@[inline] def decodeForms (tagger : PosTagger) (forms : Array String) : Array Nat :=
  tagger.hmm.decode (tagger.encodeForms forms)

/-- Decode forms and resolve every dense state to its configured POS tag name. -/
def tagForms (tagger : PosTagger) (forms : Array String) : Array String :=
  (tagger.decodeForms forms).map fun tag ↦ tagger.tagNames.getD tag ""

end PosTagger

end Nlp.Sequence
