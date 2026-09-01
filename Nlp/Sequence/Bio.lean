import Init.Data.String.Basic

/-!
# Typed BIO2 labels

BIO2 represents tokens outside an entity with `O`, starts an entity with `B-TYPE`, and continues
that same entity with `I-TYPE`. This module keeps entity types nonempty by construction, parses
only the canonical spellings, and exposes the start and transition constraints needed by a
linear-chain decoder.
-/

namespace Nlp.Sequence.Bio

/-- A nonempty named-entity type such as `PERSON` or `ORGANIZATION`. -/
structure EntityType where
  private mk ::
  /-- Exact, case-sensitive entity-type name. -/
  name : String
  /-- Canonical BIO labels never contain an empty entity type. -/
  nonempty : name ≠ ""
deriving Repr, DecidableEq

namespace EntityType

/-- Construct an entity type exactly when its name is nonempty. -/
def ofString? (name : String) : Option EntityType :=
  if nonempty : name ≠ "" then some ⟨name, nonempty⟩ else none

/-- Recover the exact name used to construct an entity type. -/
@[simp] theorem name_ofString?_eq_some (name : String) (entity : EntityType)
    (success : ofString? name = some entity) : entity.name = name := by
  by_cases nonempty : name ≠ ""
  · simp [ofString?, nonempty] at success
    exact congrArg EntityType.name success.symm
  · simp [ofString?, nonempty] at success

end EntityType

/-- One canonical BIO2 state. -/
inductive Tag where
  /-- The token is outside every named entity. -/
  | outside
  /-- The token begins an entity of the given type. -/
  | begin (entity : EntityType)
  /-- The token continues an entity of the given type. -/
  | inside (entity : EntityType)
deriving Repr, DecidableEq

/-- Why a string is not a canonical BIO2 label. -/
inductive ParseError where
  /-- A `B-` or `I-` prefix was present without an entity type. -/
  | emptyEntity (label : String)
  /-- The label was neither `O` nor a canonical `B-TYPE` or `I-TYPE`. -/
  | invalidLabel (label : String)
deriving Repr, DecidableEq

namespace Tag

/-- Render a typed tag into its canonical character sequence. -/
def renderChars : Tag → List Char
  | .outside => ['O']
  | .begin entity => 'B' :: '-' :: entity.name.toList
  | .inside entity => 'I' :: '-' :: entity.name.toList

/-- Render a typed tag as exactly `O`, `B-TYPE`, or `I-TYPE`. -/
def render (tag : Tag) : String :=
  String.ofList tag.renderChars

/-- Parse exactly the canonical BIO2 spellings. -/
def parse (label : String) : Except ParseError Tag :=
  match label.toList with
  | ['O'] => .ok .outside
  | ['B', '-'] => .error (.emptyEntity label)
  | 'B' :: '-' :: first :: rest =>
      .ok (.begin ⟨String.ofList (first :: rest), by simp⟩)
  | ['I', '-'] => .error (.emptyEntity label)
  | 'I' :: '-' :: first :: rest =>
      .ok (.inside ⟨String.ofList (first :: rest), by simp⟩)
  | _ => .error (.invalidLabel label)

/-- Rendering and then parsing recovers every typed BIO2 tag. -/
@[simp] theorem parse_render (tag : Tag) : parse tag.render = .ok tag := by
  cases tag with
  | outside => rfl
  | begin entity =>
      rcases entity with ⟨name, nonempty⟩
      have charsNonempty : name.toList ≠ [] := by
        intro empty
        apply nonempty
        rw [← String.ofList_toList (s := name), empty]
      cases chars : name.toList with
      | nil => exact absurd chars charsNonempty
      | cons first rest =>
          have reconstructed : String.ofList (first :: rest) = name := by
            rw [← chars, String.ofList_toList]
          simpa [render, renderChars, parse, chars] using reconstructed
  | inside entity =>
      rcases entity with ⟨name, nonempty⟩
      have charsNonempty : name.toList ≠ [] := by
        intro empty
        apply nonempty
        rw [← String.ofList_toList (s := name), empty]
      cases chars : name.toList with
      | nil => exact absurd chars charsNonempty
      | cons first rest =>
          have reconstructed : String.ofList (first :: rest) = name := by
            rw [← chars, String.ofList_toList]
          simpa [render, renderChars, parse, chars] using reconstructed

/-- Only `O` and `B-TYPE` may occur at the first position of a BIO2 sequence. -/
@[inline] def legalStart : Tag → Bool
  | .outside | .begin _ => true
  | .inside _ => false

/-- Check whether `next` may immediately follow `prior` under BIO2. -/
@[inline] def legalTransition : Tag → Tag → Bool
  | _, .outside => true
  | _, .begin _ => true
  | .begin prior, .inside next => prior.name == next.name
  | .inside prior, .inside next => prior.name == next.name
  | .outside, .inside _ => false

/-- Check all adjacent transitions after a known previous tag. -/
def validTail : Tag → List Tag → Bool
  | _, [] => true
  | prior, next :: rest => legalTransition prior next && validTail next rest

/-- Check the start and every adjacent transition of a BIO2 tag list. -/
def validList : List Tag → Bool
  | [] => true
  | first :: rest => legalStart first && validTail first rest

/-- Check the start and every adjacent transition of a BIO2 tag array. -/
def valid (tags : Array Tag) : Bool :=
  validList tags.toList

@[simp] theorem legalStart_outside : legalStart .outside = true := rfl

@[simp] theorem legalStart_begin (entity : EntityType) : legalStart (.begin entity) = true := rfl

@[simp] theorem legalStart_inside (entity : EntityType) :
    legalStart (.inside entity) = false := rfl

@[simp] theorem legalTransition_outside (prior : Tag) :
    legalTransition prior .outside = true := by
  cases prior <;> rfl

@[simp] theorem legalTransition_begin (prior : Tag) (entity : EntityType) :
    legalTransition prior (.begin entity) = true := by
  cases prior <;> rfl

private theorem validTail_replicate_outside (prior : Tag) (count : Nat) :
    validTail prior (List.replicate count .outside) = true := by
  induction count generalizing prior with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp [List.replicate_succ, validTail, inductionHypothesis]

/-- An arbitrary-length sequence containing only `O` is valid BIO2. -/
@[simp] theorem valid_replicate_outside (count : Nat) :
    valid (Array.replicate count .outside) = true := by
  cases count with
  | zero => rfl
  | succ count =>
      simp [valid, validList, List.replicate_succ, validTail_replicate_outside]

end Tag

end Nlp.Sequence.Bio
