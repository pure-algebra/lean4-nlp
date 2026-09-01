import Nlp.IO.ConlluReader

namespace NlpTests.IO.ConlluReader

open Nlp.IO
open Nlp.Dependency

private def row : ConlluRow :=
  { id := "1",
    form := "dogs",
    lemma := .present "dog" (by decide),
    upos := .present "NOUN" (by decide),
    xpos := .present "NNS" (by decide),
    feats := .missing,
    head := .present "0" (by decide),
    deprel := .present "root" (by decide),
    deps := .missing,
    misc := .missing }

example : row.WF := by decide

example : ConlluRow.parse 7 row.render = .ok row :=
  ConlluRow.parse_render row (by decide) 7

private def sample : String :=
  "# sent_id = demo\n# text = can't go\n" ++
  "1-2\tcan't\t_\t_\t_\t_\t_\t_\t_\tSpaceAfter=No\n" ++
  "1\tca\tcan\tAUX\tMD\t_\t3\taux\t3:aux\tSpaceAfter=No\n" ++
  "2\tn't\tnot\tPART\tRB\t_\t3\tadvmod\t3:advmod\t_\n" ++
  "3\tgo\tgo\tVERB\tVB\t_\t0\troot\t0:root\t_\n" ++
  "3.1\tghost\tghost\tX\t_\t_\t_\t_\t3:dep\t_\n\n"

private def layerOneRoundTrip : Bool :=
  match parseConllu sample with
  | .error _ => false
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      decide (UniformLineEndings sentences) && renderConllu sentences == sample &&
        sentence.lineEnding == .lf &&
        sentence.comments == #["# sent_id = demo", "# text = can't go"] &&
        match sentence.rows.toList with
        | [mwt, _, _, _, empty] =>
          mwt.id == "1-2" && mwt.lemma == .missing && empty.id == "3.1"
        | _ => false
    | _ => false

#guard layerOneRoundTrip

private def crlfSample : String :=
  "# sent_id = crlf\r\n" ++
    "1\tworks\twork\tVERB\tVBZ\t_\t0\troot\t0:root\t_\r\n\r\n"

private def crlfRoundTrip : Bool :=
  match parseConllu crlfSample with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      decide (UniformLineEndings sentences) && sentence.lineEnding == .crlf &&
        renderConllu sentences == crlfSample
    | _ => false
  | .error _ => false

#guard crlfRoundTrip

private def mixedEndingsAreNoncanonical : Bool :=
  match parseConllu sample, parseConllu crlfSample with
  | .ok lfSentences, .ok crlfSentences =>
    match lfSentences.toList, crlfSentences.toList with
    | [lfSentence], [crlfSentence] =>
      let mixed := #[lfSentence, crlfSentence]
      !decide (UniformLineEndings mixed) &&
        match parseConllu (renderConllu mixed) with
        | .error (.mixedLineEndings _ .lf .crlf) => true
        | _ => false
    | _, _ => false
  | _, _ => false

#guard mixedEndingsAreNoncanonical

#guard ConlluId.parse "7" == some (.word 7)
#guard ConlluId.parse "3-4" == some (.range 3 4)
#guard ConlluId.parse "5.1" == some (.empty 5 1)
#guard (ConlluId.parse "4-3").isNone
#guard (ConlluId.parse "5.0").isNone
#guard (ConlluId.parse "1_0").isNone
#guard ConlluId.parse "0.1" == some (.empty 0 1)
#guard (ConlluId.parse "0.0").isNone

private def secondSentence : String :=
  "# sent_id = second\n1\tdone\tdo\tVERB\tVBN\t_\t0\troot\t0:root\t_\n\n"

private def blankBoundaries : Bool :=
  match parseConllu (sample ++ secondSentence) with
  | .ok sentences => sentences.size == 2 && renderConllu sentences == sample ++ secondSentence
  | .error _ => false

#guard blankBoundaries

private def wrongColumns (count : Nat) : Bool :=
  let input := joinFields (List.replicate count "_") ++ "\n\n"
  match parseConllu input with
  | .error (.wrongColumnCount 1 found) => found == count
  | _ => false

#guard wrongColumns 9
#guard wrongColumns 11

private def rejectsEmptyField : Bool :=
  let input := joinFields ["1", "", "_", "_", "_", "_", "_", "_", "_", "_"] ++ "\n\n"
  match parseConllu input with
  | .error (.emptyField 1 2) => true
  | _ => false

#guard rejectsEmptyField

private def projectedDoc : Bool :=
  match parseConllu sample with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .ok document =>
        decide document.WF && document.text == "ca n't go" &&
          document.forms == #["ca", "n't", "go"] &&
          document.lemma == #["can", "not", "go"] &&
          document.pos == #["AUX", "PART", "VERB"] && document.head == #[3, 3, 0] &&
          document.deprel == #["aux", "advmod", "root"] &&
          document.spans == #[⟨0, 2⟩, ⟨3, 6⟩, ⟨7, 9⟩]
      | .error _ => false
    | _ => false
  | .error _ => false

#guard projectedDoc

private def malformedHead : Bool :=
  let input := "1\tdog\tdog\tNOUN\tNN\t_\tx\troot\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.malformedHead 1 "x") => true
      | _ => false
    | _ => false
  | .error _ => false

#guard malformedHead

private def headOutOfRange : Bool :=
  let input := "1\tdog\tdog\tNOUN\tNN\t_\t2\troot\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.headOutOfRange 1 2 1) => true
      | _ => false
    | _ => false
  | .error _ => false

#guard headOutOfRange

private def selfHead : Bool :=
  let input := "1\tdog\tdog\tNOUN\tNN\t_\t1\tdep\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.selfHead 1 1) => true
      | _ => false
    | _ => false
  | .error _ => false

#guard selfHead

private def noRoot : Bool :=
  let input :=
    "1\tone\tone\tNOUN\tNN\t_\t2\tdep\t_\t_\n" ++
      "2\ttwo\ttwo\tNOUN\tNN\t_\t1\tdep\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error .noRoot => true
      | _ => false
    | _ => false
  | .error _ => false

#guard noRoot

private def multipleRoots : Bool :=
  let input :=
    "1\tone\tone\tNOUN\tNN\t_\t0\troot\t_\t_\n" ++
      "2\ttwo\ttwo\tNOUN\tNN\t_\t0\troot\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.multipleRoots 1 1 2 2) => true
      | _ => false
    | _ => false
  | .error _ => false

#guard multipleRoots

private def disconnectedCycle : Bool :=
  let input :=
    "1\tone\tone\tNOUN\tNN\t_\t0\troot\t_\t_\n" ++
      "2\ttwo\ttwo\tNOUN\tNN\t_\t3\tdep\t_\t_\n" ++
      "3\tthree\tthree\tNOUN\tNN\t_\t2\tdep\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.dependencyCycle 3 3 2) => true
      | _ => false
    | _ => false
  | .error _ => false

#guard disconnectedCycle

private def rootHeadNeedsRootRelation : Bool :=
  let input := "1\tdog\tdog\tNOUN\tNN\t_\t0\tdep\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.rootRelationMismatch 1 1 0 "dep") => true
      | _ => false
    | _ => false
  | .error _ => false

#guard rootHeadNeedsRootRelation

private def rootRelationNeedsRootHead : Bool :=
  let input :=
    "1\tone\tone\tNOUN\tNN\t_\t2\troot\t_\t_\n" ++
      "2\ttwo\ttwo\tNOUN\tNN\t_\t0\troot\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.rootRelationMismatch 1 1 2 "root") => true
      | _ => false
    | _ => false
  | .error _ => false

#guard rootRelationNeedsRootHead

private def validNonprojective : Bool :=
  let input :=
    "1\tone\tone\tNOUN\tNN\t_\t3\tdep\t_\t_\n" ++
      "2\ttwo\ttwo\tNOUN\tNN\t_\t4\tdep\t_\t_\n" ++
      "3\tthree\tthree\tNOUN\tNN\t_\t0\troot\t_\t_\n" ++
      "4\tfour\tfour\tNOUN\tNN\t_\t3\tdep\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .ok document =>
        document.head == #[3, 4, 0, 3] &&
          match checkProjective document.head with
          | .error (.crossing 1 3 2 4) => true
          | _ => false
      | .error _ => false
    | _ => false
  | .error _ => false

#guard validNonprojective

private def nonsequentialWordId : Bool :=
  let input :=
    "1\tone\tone\tNOUN\tNN\t_\t0\troot\t_\t_\n" ++
      "3\tthree\tthree\tNOUN\tNN\t_\t1\tdep\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.nonsequentialWordId 2 2 3) => true
      | _ => false
    | _ => false
  | .error _ => false

#guard nonsequentialWordId

private def missingUpos : Bool :=
  let input := "1\tdog\tdog\t_\tNN\t_\t0\troot\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.missingUpos 1) => true
      | _ => false
    | _ => false
  | .error _ => false

#guard missingUpos

private def missingDeprel : Bool :=
  let input := "1\tdog\tdog\tNOUN\tNN\t_\t0\t_\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.missingDeprel 1) => true
      | _ => false
    | _ => false
  | .error _ => false

#guard missingDeprel

private def separatedHeadIsMalformed : Bool :=
  let input := "1\tdog\tdog\tNOUN\tNN\t_\t1_0\troot\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .error (.malformedHead 1 "1_0") => true
      | _ => false
    | _ => false
  | .error _ => false

#guard separatedHeadIsMalformed

private def underscoreIsMissing : Bool :=
  let input := "1\t_\t_\tNOUN\t_\t_\t0\troot\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.rows.toList, sentence.toDoc with
      | [parsed], .ok document => parsed.lemma == .missing && document.lemma == #["_"]
      | _, _ => false
    | _ => false
  | .error _ => false

#guard underscoreIsMissing

private def utf8Spans : Bool :=
  let input :=
    "1\té\té\tNOUN\t_\t_\t0\troot\t_\t_\n" ++
      "2\t猫\t猫\tNOUN\t_\t_\t1\tdep\t_\t_\n\n"
  match parseConllu input with
  | .ok sentences =>
    match sentences.toList with
    | [sentence] =>
      match sentence.toDoc with
      | .ok document => document.text == "é 猫" && document.spans == #[⟨0, 2⟩, ⟨3, 6⟩]
      | .error _ => false
    | _ => false
  | .error _ => false

#guard utf8Spans

end NlpTests.IO.ConlluReader
