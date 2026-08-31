import Nlp.Core.Layer

namespace NlpTests.Core.Layer

open Nlp

example : Sub [.tokens] [.pos, .tokens] := by decide

example : ¬ Sub [.pos] [.tokens] := by decide

example : Sub [.tokens, .pos] [.lemma, .pos, .tokens] := by decide

example : LawfulBEq Nlp.Layer := inferInstance

example : Sub ([.tokens] ++ [.pos]) [.lemma, .pos, .tokens] := by decide

end NlpTests.Core.Layer
