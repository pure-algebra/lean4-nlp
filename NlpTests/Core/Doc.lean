import Nlp.Core.Doc

namespace NlpTests.Core.Doc

open Nlp

private def semanticErrorOf : Except Doc.SemanticError α → Option Doc.SemanticError
  | .ok _ => none
  | .error cause => some cause

private def spans : Array Span := #[⟨0, 3⟩, ⟨4, 8⟩]
private def forms : Array String := #["the", "dogs"]

private def tokenDoc : Doc [.tokens] := { text := "the dogs", spans, forms }

example : tokenDoc.WF := by decide

example : tokenDoc.size = 2 := by decide

example : tokenDoc.formAt 0 = "the" := by decide

example : tokenDoc.spanAt 1 = ⟨4, 8⟩ := by decide

example : (Doc.empty "text").WF := Doc.empty_wf "text"

example : Doc.checked tokenDoc = .ok tokenDoc := by rfl

private def malformed : Doc [.tokens] :=
  { text := "the dogs", spans := #[⟨0, 3⟩], forms }

example : ¬ malformed.WF := by decide

example :
    Doc.checked malformed =
      .error (.invalidColumnSizes
        { forms := 2, spans := 1, pos := 0, lemma := 0, ner := 0, head := 0, deprel := 0 }) := by
  rfl

example : Doc.ofTokens "the dogs" spans forms = .ok tokenDoc := by rfl

example :
    semanticErrorOf (Doc.checkedSemantic malformed) =
      some (.structural (.invalidColumnSizes
        { forms := 2, spans := 1, pos := 0, lemma := 0, ner := 0, head := 0,
          deprel := 0 })) := by
  native_decide

private def tagged : Doc [.pos, .tokens] :=
  { tokenDoc with pos := #["DET", "NOUN"] }

example : tagged.WF := by decide

example : tagged.posAt 1 = "NOUN" := by decide

example : tokenDoc.SemanticWF := by native_decide

example : (Doc.checkedSemantic tokenDoc).isOk := by native_decide

example : Doc.checkedSemantic tokenDoc = .ok tokenDoc :=
  (Doc.checkedSemantic_eq_ok_iff tokenDoc).2 (by native_decide)

example : tokenDoc.originalAt? 0 = some "the" := by native_decide

example : tokenDoc.originalAt? 1 = some "dogs" := by native_decide

example : tokenDoc.originalAt? 2 = none := by native_decide

private def emojiDoc : Doc [.tokens] :=
  { text := "a😀猫", spans := #[⟨0, 1⟩, ⟨1, 5⟩, ⟨5, 8⟩], forms := #["a", "😀", "猫"] }

example : emojiDoc.SemanticWF := by native_decide

example : emojiDoc.originalAt? 0 = some "a" := by native_decide

example : emojiDoc.originalAt? 1 = some "😀" := by native_decide

example : emojiDoc.originalAt? 2 = some "猫" := by native_decide

private def emptyForm : Doc [.tokens] :=
  { text := "a", spans := #[⟨0, 1⟩], forms := #[""] }

example : ¬emptyForm.SemanticWF := by native_decide

example : semanticErrorOf (Doc.checkedSemantic emptyForm) = some (.emptyTokenForm 0) := by
  native_decide

private def emptySpan : Doc [.tokens] :=
  { text := "a", spans := #[⟨0, 0⟩], forms := #["a"] }

example : ¬emptySpan.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic emptySpan) = some (.emptyTokenSpan 0 ⟨0, 0⟩) := by
  native_decide

private def reversedSpan : Doc [.tokens] :=
  { text := "ab", spans := #[⟨2, 1⟩], forms := #["a"] }

example : ¬reversedSpan.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic reversedSpan) =
      some (.reversedTokenSpan 0 ⟨2, 1⟩) := by
  native_decide

private def outOfBounds : Doc [.tokens] :=
  { text := "a", spans := #[⟨0, 2⟩], forms := #["a"] }

example : ¬outOfBounds.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic outOfBounds) =
      some (.tokenSpanOutOfBounds 0 ⟨0, 2⟩ 1) := by
  native_decide

private def midCodepointBegin : Doc [.tokens] :=
  { text := "😀", spans := #[⟨1, 4⟩], forms := #["😀"] }

example : ¬midCodepointBegin.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic midCodepointBegin) =
      some (.tokenSpanNotUtf8Boundary 0 .begin 1) := by
  native_decide

example : midCodepointBegin.originalAt? 0 = none := by native_decide

private def midCodepointEnd : Doc [.tokens] :=
  { text := "😀", spans := #[⟨0, 3⟩], forms := #["😀"] }

example : ¬midCodepointEnd.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic midCodepointEnd) =
      some (.tokenSpanNotUtf8Boundary 0 .end 3) := by
  native_decide

private def overlapping : Doc [.tokens] :=
  { text := "abcd", spans := #[⟨0, 3⟩, ⟨2, 4⟩], forms := #["abc", "cd"] }

example : ¬overlapping.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic overlapping) =
      some (.overlappingTokenSpans 0 ⟨0, 3⟩ ⟨2, 4⟩) := by
  native_decide

private def mixedTokenErrors : Doc [.tokens] :=
  { text := "ab", spans := #[⟨0, 0⟩, ⟨1, 2⟩], forms := #["a", ""] }

example :
    semanticErrorOf (Doc.checkedSemantic mixedTokenErrors) = some (.emptyTokenForm 1) := by
  native_decide

private def mixedSpanErrors : Doc [.tokens] :=
  { text := "ab", spans := #[⟨2, 1⟩, ⟨1, 1⟩], forms := #["a", "b"] }

example :
    semanticErrorOf (Doc.checkedSemantic mixedSpanErrors) = some (.emptyTokenSpan 1 ⟨1, 1⟩) := by
  native_decide

private def mixedBoundaryErrors : Doc [.tokens] :=
  { text := "😀😀", spans := #[⟨0, 3⟩, ⟨5, 8⟩], forms := #["😀", "😀"] }

example :
    semanticErrorOf (Doc.checkedSemantic mixedBoundaryErrors) =
      some (.tokenSpanNotUtf8Boundary 1 .begin 5) := by
  native_decide

private def sentenceDoc : Doc [.sents, .tokens] :=
  { text := "One. Two.", spans := #[⟨0, 4⟩, ⟨5, 9⟩], forms := #["One.", "Two."],
    sentEnd := #[1, 2] }

example : sentenceDoc.SemanticWF := by native_decide

private def dependencyDoc : Doc [.dep, .tokens] :=
  { tokenDoc with head := #[2, 0], deprel := #["det", "root"] }

example : dependencyDoc.SemanticWF := by native_decide

example (semantic : dependencyDoc.SemanticWF) : dependencyDoc.DependencyWF :=
  Doc.semanticWF_dependency semantic (by decide)

private def cyclicDependency : Doc [.dep, .tokens] :=
  { text := "a b c", spans := #[⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩], forms := #["a", "b", "c"],
    head := #[0, 3, 2], deprel := #["root", "dep", "dep"] }

example : ¬cyclicDependency.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic cyclicDependency) =
      some (.invalidDependencyTree (.cycle 3 2)) := by
  native_decide

private def dependencyWithoutTokens : Doc [.dep] := { text := "" }

example : ¬dependencyWithoutTokens.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic dependencyWithoutTokens) =
      some .dependencyLayerRequiresTokens := by
  native_decide

private def sentenceLocalDependencies : Doc [.dep, .sents, .tokens] :=
  { text := "a b c d", spans := #[⟨0, 1⟩, ⟨2, 3⟩, ⟨4, 5⟩, ⟨6, 7⟩],
    forms := #["a", "b", "c", "d"], sentEnd := #[2, 4],
    head := #[0, 1, 2, 0], deprel := #["root", "dep", "dep", "root"] }

example : sentenceLocalDependencies.SemanticWF := by native_decide

private def badSecondDependency : Doc [.dep, .sents, .tokens] :=
  { sentenceLocalDependencies with head := #[0, 1, 2, 1] }

example :
    semanticErrorOf (Doc.checkedSemantic badSecondDependency) =
      some (.invalidDependencyDocument (.sentence 1 2 4 .noRoot)) := by
  native_decide

private def sentenceWithoutTokens : Doc [.sents] := { text := "" }

example : ¬sentenceWithoutTokens.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic sentenceWithoutTokens) =
      some .sentenceLayerRequiresTokens := by
  native_decide

private def emptySentenceDoc : Doc [.sents, .tokens] := { text := "" }

example : emptySentenceDoc.SemanticWF := by native_decide

private def sentenceEndsForEmpty : Doc [.sents, .tokens] := { text := "", sentEnd := #[0] }

example : ¬sentenceEndsForEmpty.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic sentenceEndsForEmpty) =
      some (.sentenceEndsForEmptyTokens #[0]) := by
  native_decide

private def missingSentenceEnd : Doc [.sents, .tokens] :=
  { text := "a", spans := #[⟨0, 1⟩], forms := #["a"] }

example : ¬missingSentenceEnd.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic missingSentenceEnd) = some (.missingSentenceEnd 1) := by
  native_decide

private def nonIncreasingEnds : Doc [.sents, .tokens] :=
  { sentenceDoc with sentEnd := #[1, 1] }

example : ¬nonIncreasingEnds.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic nonIncreasingEnds) =
      some (.nonIncreasingSentenceEnds 0 1 1) := by
  native_decide

private def zeroSentenceEnd : Doc [.sents, .tokens] :=
  { sentenceDoc with sentEnd := #[0, 2] }

example : ¬zeroSentenceEnd.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic zeroSentenceEnd) = some (.emptySentence 0) := by
  native_decide

private def sentenceEndOutOfBounds : Doc [.sents, .tokens] :=
  { sentenceDoc with sentEnd := #[1, 3] }

example : ¬sentenceEndOutOfBounds.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic sentenceEndOutOfBounds) =
      some (.sentenceEndOutOfBounds 1 3 2) := by
  native_decide

private def mixedSentenceErrors : Doc [.sents, .tokens] :=
  { sentenceDoc with sentEnd := #[3, 0] }

example :
    semanticErrorOf (Doc.checkedSemantic mixedSentenceErrors) = some (.emptySentence 1) := by
  native_decide

private def mixedSentenceOrderErrors : Doc [.sents, .tokens] :=
  { sentenceDoc with sentEnd := #[2, 3, 1] }

example :
    semanticErrorOf (Doc.checkedSemantic mixedSentenceOrderErrors) =
      some (.sentenceEndOutOfBounds 1 3 2) := by
  native_decide

private def wrongFinalSentenceEnd : Doc [.sents, .tokens] :=
  { sentenceDoc with sentEnd := #[1] }

example : ¬wrongFinalSentenceEnd.SemanticWF := by native_decide

example :
    semanticErrorOf (Doc.checkedSemantic wrongFinalSentenceEnd) =
      some (.finalSentenceEnd 2 1) := by
  native_decide

end NlpTests.Core.Doc
