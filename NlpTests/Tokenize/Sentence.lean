import Nlp.Tokenize.Scanner
import Nlp.Tokenize.Sentence

namespace NlpTests.Tokenize.Sentence

open Nlp.Tokenize

private def ends (text : String) (config : Sentence.Config := {})
    (tokenConfig : Config := {}) : Array Nat :=
  (Sentence.split (tokenize text tokenConfig) config).ends

example : ends "" = #[] := by native_decide

example : ends "Hi. Bye!" = #[2, 4] := by native_decide

example : ends "Really?! Yes..." = #[2, 4] := by native_decide

example :
    ends "Really?! Yes..." {} { mode := .whitespace } = #[1, 2] := by
  native_decide

example :
    ends "Hi. Bye!" {} { mode := .whitespace } = #[1, 2] := by
  native_decide

example : ends "The U.S. policy changed." = #[5] := by native_decide

example : ends "Hi.) Bye." = #[3, 5] := by native_decide

example : ends "Hi. \"Bye.\"" = #[2, 6] := by native_decide

example : ends "Hi. ! Bye" = #[2, 3, 4] := by native_decide

example : ends "你好。再见！" = #[2, 4] := by native_decide

example : ends "مرحبا؟ التالي." = #[2, 4] := by native_decide

example : ends "الأول۔ التالي۔" = #[2, 4] := by native_decide

example : ends "One\nTwo" = #[2] := by native_decide

example :
    ends "One\nTwo" { newlinePolicy := .always } = #[1, 2] := by
  native_decide

example :
    ends "One\u000bTwo\u000cThree" { newlinePolicy := .always } = #[1, 2, 3] := by
  native_decide

example :
    ends "One\n\nTwo" { newlinePolicy := .two } = #[1, 2] := by
  native_decide

example :
    ends "One\r\nTwo" { newlinePolicy := .two } = #[2] := by
  native_decide

private def splitCrLf : Tokenization :=
  let text := "A\r\nB"
  let p0 := text.startPos
  have h0 : p0 ≠ text.endPos := by decide
  let p1 := p0.next h0
  have h1 : p1 ≠ text.endPos := by decide +revert
  let p2 := p1.next h1
  have h2 : p2 ≠ text.endPos := by decide +revert
  let p3 := p2.next h2
  have h3 : p3 ≠ text.endPos := by decide +revert
  let p4 := p3.next h3
  { text
    tokens := #[Token.ofPositions p0 p1 String.Pos.lt_next .word,
      Token.ofPositions p1 p2 String.Pos.lt_next .newline,
      Token.ofPositions p2 p3 String.Pos.lt_next .newline,
      Token.ofPositions p3 p4 String.Pos.lt_next .word] }

example : (Sentence.split splitCrLf { newlinePolicy := .two }).ends = #[4] := by
  native_decide

example : (Sentence.split splitCrLf { newlinePolicy := .always }).ends = #[3, 4] := by
  native_decide

example :
    ends "One\r\n\r\nTwo" { newlinePolicy := .two } = #[1, 2] := by
  native_decide

example :
    ends "One\nTwo. Three" { mode := .eolOnly } = #[1, 4] := by
  native_decide

example :
    ends "One. Two!" { mode := .oneSentence } = #[4] := by
  native_decide

example :
    ends "a\r\nb" { newlinePolicy := .always }
      { mode := .whitespace, keepNewlines := true } = #[2, 3] := by
  native_decide

example :
    ends "\nHello" { newlinePolicy := .always } { keepNewlines := true } = #[2] := by
  native_decide

example :
    ends "\n\nHello" { newlinePolicy := .two } { keepNewlines := true } = #[3] := by
  native_decide

example :
    ends "\n\n" { newlinePolicy := .two } { keepNewlines := true } = #[2] := by
  native_decide

example :
    ends "A\n\nB" { newlinePolicy := .always } { keepNewlines := true } = #[2, 4] := by
  native_decide

example :
    ends "A\n\n" { newlinePolicy := .always } { keepNewlines := true } = #[3] := by
  native_decide

example :
    ends "Hi.\nBye" {} { keepNewlines := true } = #[3, 4] := by
  native_decide

example :
    ends "Hi.\nBye" { newlinePolicy := .always } { keepNewlines := true } = #[3, 4] := by
  native_decide

private def sentenceDenseText : String :=
  String.join (List.replicate 2048 "x. ")

example : (Sentence.split (tokenize sentenceDenseText)).ends.size = 2048 := by
  native_decide

private def sample : Sentence.Segmentation :=
  Sentence.split (tokenize "One. Two.")

example : sample.ends = #[2, 4] := by native_decide
example : sample.rangeAt? 0 = some (0, 2) := by native_decide
example : sample.rangeAt? 1 = some (2, 4) := by native_decide
example : sample.rangeAt? 2 = none := by native_decide

example (source : Tokenization) (config : Sentence.Config) :
    (Sentence.split source config).WF :=
  Sentence.split_wf source config

private def reordered : Tokenization :=
  let source := tokenize "a b c"
  { source with tokens := source.tokens.reverse }

example : (Sentence.split reordered).ends = #[3] := by native_decide
example : (Sentence.split reordered).WF := Sentence.split_wf reordered

end NlpTests.Tokenize.Sentence
