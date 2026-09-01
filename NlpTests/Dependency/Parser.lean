import Nlp.Dependency.Parser

/-! Functional parser-model and zero-copy sentence-view regression tests. -/

namespace NlpTests.Dependency.Parser

open Nlp Nlp.Dependency

private def forms : Array String := #["the", "dogs", "run", "."]
private def pos : Array String := #["DET", "NOUN", "VERB", "PUNCT"]

private def viewChecks : Bool :=
  match Sentence.ofRange forms pos 1 3 with
  | .error _ => false
  | .ok sentence =>
      sentence.size == 2 && sentence.form? 1 == some "dogs" &&
        sentence.pos? 2 == some "VERB" && (sentence.form? 0).isNone &&
        (sentence.form? 3).isNone

#guard viewChecks

#guard match Sentence.ofRange forms #["DET"] 0 1 with
  | .error (.columnCount 4 1) => true
  | _ => false

#guard match Sentence.ofRange forms pos 3 2 with
  | .error (.invalidRange 3 2 4) => true
  | _ => false

private def scorer (sentence : Sentence) (head dependent relation : Nat) : Float :=
  if head = 0 then
    if sentence.pos? dependent == some "VERB" then 0.0 else 20.0
  else if relation = 1 then
    if sentence.pos? head == some "VERB" then 1.0 else 4.0
  else
    8.0

private def parser : Except ArcScoreError Parser :=
  Parser.compile #["root", "dep"] 0 scorer

private def parsedColumns : Bool :=
  match parser with
  | .error _ => false
  | .ok model =>
      match model.parseArrays? forms pos with
      | .ok (some result) =>
          result.heads.size == forms.size && result.relations.size == forms.size &&
            result.heads[2]? == some 0 && result.relations[2]? == some "root"
      | _ => false

#guard parsedColumns

private def scorerSeesRangeWithoutCopies : Bool :=
  match parser, Sentence.ofRange forms pos 1 3 with
  | .ok model, .ok sentence =>
      match model.parse? sentence with
      | .ok (some result) =>
          result.heads.size == 2 && result.relations == #["dep", "root"]
      | _ => false
  | _, _ => false

#guard scorerSeesRangeWithoutCopies

private def invalidDynamicScoreRetainsCoordinates : Bool :=
  match Parser.compile #["root", "dep"] 0 fun _ head dependent relation =>
      if head = 0 && dependent = 1 && relation = 0 then -1.0 else 0.0 with
  | .error _ => false
  | .ok model =>
      match model.parseArrays? #["x"] #["X"] with
      | .error (.scores (.invalidCost 0 1 0 value _)) => value.toBits == (-1.0).toBits
      | _ => false

#guard invalidDynamicScoreRetainsCoordinates

end NlpTests.Dependency.Parser
