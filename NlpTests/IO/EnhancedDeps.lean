import Nlp.IO.EnhancedDeps

/-!
# Typed enhanced-dependency codec tests

The graph fixture follows the coordination pattern used by the Universal Dependencies enhanced
syntax documentation: “They buy and sell books” propagates the subject and object to both verbs.
-/

namespace NlpTests.IO.EnhancedDeps

open Nlp.Dependency Nlp.IO

private def sameDepsResult
    (left right : Except DepsError (Option (Array EnhancedArc))) : Bool :=
  match left, right with
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

private def canonicalDeps : Option (Array EnhancedArc) :=
  some #[⟨.root, "root"⟩, ⟨.word 2, "nsubj"⟩,
    ⟨.word 2, "nsubj:pass:xsubj"⟩, ⟨.empty 5 1, "conj"⟩]

example : DepsWF canonicalDeps := by native_decide

example : renderDeps canonicalDeps = "0:root|2:nsubj|2:nsubj:pass:xsubj|5.1:conj" := by
  native_decide

example : sameDepsResult (parseDeps (renderDeps canonicalDeps)) (.ok canonicalDeps) := by
  native_decide

example : sameDepsResult (parseDeps "_") (.ok none) := by native_decide

example : sameDepsResult (parseDeps "2:nsubj|2:nsubj:xsubj")
    (.ok (some #[⟨.word 2, "nsubj"⟩, ⟨.word 2, "nsubj:xsubj"⟩])) := by
  native_decide

example : sameDepsResult (parseDeps "3:nsubj:pass:xsubj")
    (.ok (some #[⟨.word 3, "nsubj:pass:xsubj"⟩])) := by
  native_decide

example : sameDepsResult (parseDeps "5.1:conj")
    (.ok (some #[⟨.empty 5 1, "conj"⟩])) := by
  native_decide

example : sameDepsResult (parseDeps "") (.error .emptyPresentField) := by native_decide

example : sameDepsResult (parseDeps "|1:dep") (.error (.emptyItem 0)) := by native_decide

example : sameDepsResult (parseDeps "1:dep|") (.error (.emptyItem 1)) := by native_decide

example : sameDepsResult (parseDeps "1dep") (.error (.missingSeparator 0 "1dep")) := by
  native_decide

example : sameDepsResult (parseDeps ":dep") (.error (.emptyHead 0)) := by native_decide

example : sameDepsResult (parseDeps "1:") (.error (.emptyRelation 0 (.word 1))) := by
  native_decide

example : sameDepsResult (parseDeps "x:dep") (.error (.malformedHead 0 "x")) := by
  native_decide

example : sameDepsResult (parseDeps "1-2:dep") (.error (.rangeHead 0 1 2)) := by
  native_decide

example : sameDepsResult (parseDeps "1.1.1:dep") (.error (.copyHead 0 "1.1.1")) := by
  native_decide

example : sameDepsResult (parseDeps "2:dep|1:dep")
    (.error (.noncanonicalHeadOrder 1 (.word 2) (.word 1))) := by
  native_decide

example : sameDepsResult (parseDeps "1:dep|1:dep")
    (.error (.duplicateArc 0 1 (.word 1) "dep")) := by
  native_decide

example : sameDepsResult (parseDeps "01:dep|1:dep")
    (.error (.duplicateArc 0 1 (.word 1) "dep")) := by
  native_decide

example : sameDepsResult (parseDeps "1:bad label")
    (.error (.invalidRelation 0 "bad label")) := by
  native_decide

example : sameDepsResult (parseDeps "1::dep") (.error (.invalidRelation 0 ":dep")) := by
  native_decide

example : sameDepsResult (parseDeps "_:dep") (.error (.malformedHead 0 "_")) := by
  native_decide

private def coordinated : String :=
  "# text = They buy and sell books\n" ++
    "1\tThey\tthey\tPRON\tPRP\t_\t2\tnsubj\t2:nsubj|4:nsubj\t_\n" ++
    "2\tbuy\tbuy\tVERB\tVBP\t_\t0\troot\t0:root\t_\n" ++
    "3\tand\tand\tCCONJ\tCC\t_\t4\tcc\t4:cc\t_\n" ++
    "4\tsell\tsell\tVERB\tVBP\t_\t2\tconj\t2:conj\t_\n" ++
    "5\tbooks\tbook\tNOUN\tNNS\t_\t2\tobj\t2:obj|4:obj\t_\n\n"

private def coordinatedReentrancy : Bool :=
  match parseConllu coordinated with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .ok (some graph) =>
      graph.nodeCount == 5 && graph.edgeCount == 7 &&
        match graph.incoming? (.word 1), graph.incoming? (.word 5) with
        | some subject, some object =>
          subject.incoming.map (·.head) == #[.word 2, .word 4] &&
            object.incoming.map (·.head) == #[.word 2, .word 4] &&
            subject.incoming.all (·.origin == .enhanced)
        | _, _ => false
    | _ => false
  | _ => false

#guard coordinatedReentrancy

private def withEmptyNode : String :=
  "1\tI\tI\tPRON\tPRP\t_\t2\tnsubj\t2:nsubj\t_\n" ++
    "2\tsaw\tsee\tVERB\tVBD\t_\t0\troot\t0:root\t_\n" ++
    "3\thim\the\tPRON\tPRP\t_\t2\tobj\t2:obj\t_\n" ++
    "4\tand\tand\tCCONJ\tCC\t_\t2\tcc\t2:cc\t_\n" ++
    "5\tyou\tyou\tPRON\tPRP\t_\t2\tconj\t2:conj\t_\n" ++
    "5.1\tsaw\tsee\tVERB\tVBD\t_\t_\t_\t2:conj\tCopyOf=2\n\n"

private def preservesEmptyNode : Bool :=
  match parseConllu withEmptyNode with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .ok (some graph) =>
      graph.nodeCount == 6 &&
        match graph.incoming? (.empty 5 1) with
        | some row => row.incoming == #[⟨.word 2, "conj", .enhanced⟩]
        | none => false
    | _ => false
  | _ => false

#guard preservesEmptyNode

private def sequentialEmptyNodes : String :=
  "0.1\tzero-one\tzero-one\tX\t_\t_\t_\t_\t1:dep\t_\n" ++
    "0.2\tzero-two\tzero-two\tX\t_\t_\t_\t_\t1:dep\t_\n" ++
    "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "1.1\tone-one\tone-one\tX\t_\t_\t_\t_\t1:dep\t_\n" ++
    "1.2\tone-two\tone-two\tX\t_\t_\t_\t_\t1:dep\t_\n" ++
    "2\ttwo\ttwo\tNOUN\tNN\t_\t1\tdep\t1:dep\t_\n" ++
    "2.1\ttwo-one\ttwo-one\tX\t_\t_\t_\t_\t2:dep\t_\n\n"

private def acceptsSequentialEmptyNodes : Bool :=
  match parseConllu sequentialEmptyNodes with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .ok (some graph) =>
      graph.nodes == #[.empty 0 1, .empty 0 2, .word 1, .empty 1 1,
        .empty 1 2, .word 2, .empty 2 1]
    | _ => false
  | _ => false

#guard acceptsSequentialEmptyNodes

private def wordIdGap : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "3\tthree\tthree\tNOUN\tNN\t_\t1\tdep\t1:dep\t_\n\n"

private def rejectsWordIdGap : Bool :=
  match parseConllu wordIdGap with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.nonsequentialWordId 2 2 3) => true
    | _ => false
  | _ => false

#guard rejectsWordIdGap

private def futureEmptyAnchor : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "2.1\tghost\tghost\tX\t_\t_\t_\t_\t1:dep\t_\n" ++
    "2\ttwo\ttwo\tNOUN\tNN\t_\t1\tdep\t1:dep\t_\n\n"

private def rejectsFutureEmptyAnchor : Bool :=
  match parseConllu futureEmptyAnchor with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.invalidEmptyNodeAnchor 2 (some 1) 2) => true
    | _ => false
  | _ => false

#guard rejectsFutureEmptyAnchor

private def emptyIdGap : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "1.1\tfirst\tfirst\tX\t_\t_\t_\t_\t1:dep\t_\n" ++
    "1.3\tthird\tthird\tX\t_\t_\t_\t_\t1:dep\t_\n\n"

private def rejectsEmptyIdGap : Bool :=
  match parseConllu emptyIdGap with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.nonsequentialEmptyNodeId 3 1 2 3) => true
    | _ => false
  | _ => false

#guard rejectsEmptyIdGap

private def emptyAfterRange : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "2-3\ttwo-three\t_\t_\t_\t_\t_\t_\t_\t_\n" ++
    "1.1\tlate\tlate\tX\t_\t_\t_\t_\t1:dep\t_\n" ++
    "2\ttwo\ttwo\tNOUN\tNN\t_\t1\tdep\t1:dep\t_\n" ++
    "3\tthree\tthree\tNOUN\tNN\t_\t1\tdep\t1:dep\t_\n\n"

private def rejectsEmptyAfterRange : Bool :=
  match parseConllu emptyAfterRange with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.invalidEmptyNodeAnchor 3 none 1) => true
    | _ => false
  | _ => false

#guard rejectsEmptyAfterRange

private def reachableCycle : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root|2:dep\t_\n" ++
    "2\ttwo\ttwo\tNOUN\tNN\t_\t1\tdep\t1:dep\t_\n\n"

private def acceptsReachableCycle : Bool :=
  match parseConllu reachableCycle with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .ok (some graph) => graph.nodeCount == 2 && graph.edgeCount == 3
    | _ => false
  | _ => false

#guard acceptsReachableCycle

private def multipleRoots : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "2\ttwo\ttwo\tNOUN\tNN\t_\t0\troot\t0:root\t_\n\n"

private def acceptsMultipleRoots : Bool :=
  match parseConllu multipleRoots with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .ok (some graph) => graph.nodeCount == 2 && graph.heads == #[.root, .root]
    | _ => false
  | _ => false

#guard acceptsMultipleRoots

private def mixedPresence : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "2\ttwo\ttwo\tNOUN\tNN\t_\t1\tdep\t_\t_\n\n"

private def rejectsMixedPresence : Bool :=
  match parseConllu mixedPresence with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.mixedDepsPresence 1 2) => true
    | _ => false
  | _ => false

#guard rejectsMixedPresence

private def allMissing : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t_\t_\n" ++
    "2\ttwo\ttwo\tNOUN\tNN\t_\t1\tdep\t_\t_\n\n"

private def unspecifiedIsNotEmpty : Bool :=
  match parseConllu allMissing with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .ok none => true
    | _ => false
  | _ => false

#guard unspecifiedIsNotEmpty

private def emptyHeadPresent : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "1.1\tghost\tghost\tVERB\tVB\t_\t1\t_\t1:dep\t_\n\n"

private def rejectsEmptyHead : Bool :=
  match parseConllu emptyHeadPresent with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.emptyNodeHeadPresent 2 "1") => true
    | _ => false
  | _ => false

#guard rejectsEmptyHead

private def emptyDeprelPresent : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root\t_\n" ++
    "1.1\tghost\tghost\tVERB\tVB\t_\t_\tdep\t1:dep\t_\n\n"

private def rejectsEmptyDeprel : Bool :=
  match parseConllu emptyDeprelPresent with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.emptyNodeDeprelPresent 2 "dep") => true
    | _ => false
  | _ => false

#guard rejectsEmptyDeprel

private def missingEndpoint : String :=
  "1\tone\tone\tNOUN\tNN\t_\t0\troot\t0:root|3:dep\t_\n\n"

private def rejectsMissingEndpoint : Bool :=
  match parseConllu missingEndpoint with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .error (.graph (.missingHead (.word 1) (.word 3))) => true
    | _ => false
  | _ => false

#guard rejectsMissingEndpoint

private def ignoredRangeDeps : String :=
  "1-2\tcan't\t_\t_\t_\t_\t_\t_\t9:ignored\t_\n" ++
    "1\tca\tcan\tAUX\tMD\t_\t2\taux\t_\t_\n" ++
    "2\tgo\tgo\tVERB\tVB\t_\t0\troot\t_\t_\n\n"

private def rangeRowsDoNotSetPresence : Bool :=
  match parseConllu ignoredRangeDeps with
  | .ok #[sentence] =>
    match sentence.toDependencyGraph with
    | .ok none => true
    | _ => false
  | _ => false

#guard rangeRowsDoNotSetPresence

end NlpTests.IO.EnhancedDeps
