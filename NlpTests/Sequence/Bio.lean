import Nlp.Sequence.Bio

namespace NlpTests.Sequence.Bio

open Nlp.Sequence.Bio

/-- A fixture helper whose fallback is unreachable for canonical test labels. -/
private def parsed (label : String) : Tag :=
  match Tag.parse label with
  | .ok tag => tag
  | .error _ => .outside

private def parsesOutside : Bool :=
  match Tag.parse "O" with
  | .ok .outside => true
  | _ => false

private def parsesAndRenders (label : String) : Bool :=
  match Tag.parse label with
  | .ok tag => tag.render == label
  | .error _ => false

private def reportsInvalid (label : String) : Bool :=
  match Tag.parse label with
  | .error (.invalidLabel found) => found == label
  | _ => false

private def reportsEmptyEntity (label : String) : Bool :=
  match Tag.parse label with
  | .error (.emptyEntity found) => found == label
  | _ => false

#guard parsesOutside
#guard parsesAndRenders "B-PERSON"
#guard parsesAndRenders "I-ORGANIZATION"

#guard reportsInvalid ""
#guard reportsInvalid "PERSON"
#guard reportsInvalid "b-PERSON"
#guard reportsInvalid "B_PERSON"
#guard reportsEmptyEntity "B-"
#guard reportsEmptyEntity "I-"

#guard Tag.legalStart (parsed "O")
#guard Tag.legalStart (parsed "B-PERSON")
#guard !(Tag.legalStart (parsed "I-PERSON"))
#guard Tag.legalTransition (parsed "B-PERSON") (parsed "I-PERSON")
#guard Tag.legalTransition (parsed "I-PERSON") (parsed "I-PERSON")
#guard !(Tag.legalTransition (parsed "B-ORGANIZATION") (parsed "I-PERSON"))
#guard !(Tag.legalTransition (parsed "O") (parsed "I-PERSON"))
#guard Tag.legalTransition (parsed "I-PERSON") (parsed "B-PERSON")
#guard Tag.legalTransition (parsed "I-PERSON") (parsed "O")

#guard Tag.valid #[]
#guard Tag.valid #[parsed "O", parsed "B-PERSON", parsed "I-PERSON", parsed "O"]
#guard Tag.valid #[parsed "B-PERSON", parsed "B-PERSON"]
#guard !(Tag.valid #[parsed "I-PERSON"])
#guard !(Tag.valid #[parsed "B-ORGANIZATION", parsed "I-PERSON"])

/-- Typed tags always survive their canonical string boundary. -/
example (tag : Tag) : Tag.parse tag.render = .ok tag :=
  Tag.parse_render tag

/-- The universal outside path is valid at every requested length. -/
example (count : Nat) : Tag.valid (Array.replicate count .outside) = true :=
  Tag.valid_replicate_outside count

end NlpTests.Sequence.Bio
