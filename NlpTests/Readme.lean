import Nlp

/-! The public README example, compiled and checked as part of `NlpTests`. -/

namespace NlpTests.Readme

open Nlp Nlp.Sequence Nlp.Tokenize

private def training : Array (Array (Tok × Nat)) :=
  #[#[(10, 0), (11, 1)], #[(10, 0), (11, 1)], #[(10, 0), (10, 0)]]

private def decoded : Array Nat :=
  let model := Hmm.estimate training 2
  model.decode #[10, 11]

example : decoded = #[0, 1] := by native_decide

private def tokenized : Doc [.sents, .tokens] :=
  Tokenizer.default.process "Hi. Bye!"

example : tokenized.forms = #["Hi", ".", "Bye", "!"] := by native_decide
example : tokenized.sentEnd = #[2, 4] := by native_decide

end NlpTests.Readme
