import Nlp.Tokenize.Scanner

namespace NlpTests.Tokenize.Scanner

open Nlp Nlp.Tokenize

private def forms (text : String) (config : Config := {}) : Array String :=
  (tokenize text config).forms

private def spans (text : String) (config : Config := {}) : Array Span :=
  (tokenize text config).spans

private def kinds (text : String) (config : Config := {}) : Array TokenKind :=
  (tokenize text config).kinds

example : forms "" = #[] := by native_decide

example : forms " \t\u000b\u000c\r\n\u00a0" = #[] := by native_decide

example :
    forms "Marie was born in Paris." = #["Marie", "was", "born", "in", "Paris", "."] := by
  native_decide

example :
    spans "Marie was born in Paris." =
      #[⟨0, 5⟩, ⟨6, 9⟩, ⟨10, 14⟩, ⟨15, 17⟩, ⟨18, 23⟩, ⟨23, 24⟩] := by
  native_decide

example : forms "she's can't won't they've I'm he'd" =
    #["she", "'s", "ca", "n't", "wo", "n't", "they", "'ve", "I", "'m", "he", "'d"] := by
  native_decide

example : forms "cannot gonna wanna gotta lemme gimme d'ye" =
    #["can", "not", "gon", "na", "wan", "na", "got", "ta", "lem", "me", "gim", "me",
      "d'", "ye"] := by
  native_decide

example : forms "U.S. paid 1,234.50 at 12:30." =
    #["U.S.", "paid", "1,234.50", "at", "12:30", "."] := by
  native_decide

private def webText : String :=
  "Visit https://example.com/a?x=1&y=2. Mail a+b@example.co.uk, @lean_4 #Lean4!"

example : forms webText =
    #["Visit", "https://example.com/a?x=1&y=2", ".", "Mail", "a+b@example.co.uk", ",",
      "@lean_4", "#Lean4", "!"] := by
  native_decide

example : kinds webText =
    #[.word, .url, .punctuation, .word, .email, .punctuation, .handle, .hashtag,
      .punctuation] := by
  native_decide

example : forms "Open https://example.com/café now." =
    #["Open", "https://example.com/café", "now", "."] := by
  native_decide

private def noWeb : WebConfig := {
  recognizeUrls := false
  recognizeEmails := false
  recognizeHandles := false
  recognizeHashtags := false
}

example : forms "https://example.com" { web := noWeb } =
    #["https", ":", "/", "/", "example.com"] := by
  native_decide

example : forms "https://example.com" { mode := .whitespace } =
    #["https://example.com"] := by
  native_decide

example : forms "Wait... really?! -- yes." =
    #["Wait", "...", "really", "?!", "--", "yes", "."] := by
  native_decide

example :
    forms "school-aged and/or" = #["school", "-", "aged", "and", "/", "or"] := by
  native_decide

example :
    forms "school-aged and/or" { splitHyphenated := false, splitForwardSlash := false } =
      #["school-aged", "and/or"] := by
  native_decide

example :
    forms "hello,world" { mode := .whitespace } = #["hello,world"] := by
  native_decide

example : forms "A 😀猫 e\u0301." = #["A", "😀", "猫", "e\u0301", "."] := by
  native_decide

example : forms "¿Otra oración? ¡Hola! «quoted»" =
    #["¿", "Otra", "oración", "?", "¡", "Hola", "!", "«", "quoted", "»"] := by
  native_decide

example : forms "€5 £5 ¥5 © × ÷" =
    #["€", "5", "£", "5", "¥", "5", "©", "×", "÷"] := by
  native_decide

example : kinds "€5 £5 ¥5 © × ÷" =
    #[.symbol, .number, .symbol, .number, .symbol, .number, .symbol, .symbol,
      .symbol] := by
  native_decide

example : forms "$€ €$ $$ +→ →+ $😀 😀$ #€ €# ##" =
    #["$€", "€$", "$$", "+→", "→+", "$😀", "😀$", "#€", "€#", "##"] := by
  native_decide

example : kinds "١٢٣ १२३ １２３ 1٢" = #[.number, .number, .number, .number] := by
  native_decide

example : kinds "ℝ ™" = #[.word, .symbol] := by native_decide

example : forms "می‌خواهم 時々 ＄＋" = #["می‌خواهم", "時々", "＄＋"] := by
  native_decide

example : kinds "می‌خواهم 時々 ＄＋" = #[.word, .word, .symbol] := by
  native_decide

example :
    spans "A 😀猫 e\u0301." =
      #[⟨0, 1⟩, ⟨2, 6⟩, ⟨6, 9⟩, ⟨10, 13⟩, ⟨13, 14⟩] := by
  native_decide

example :
    kinds "A 😀猫 3.5!" =
      #[.word, .symbol, .word, .number, .punctuation] := by
  native_decide

private def newlineConfig : Config := { mode := .whitespace, keepNewlines := true }

example : forms "a\r\nb\nc\rd\u2028e" newlineConfig =
    #["a", "\r\n", "b", "\n", "c", "\r", "d", "\u2028", "e"] := by
  native_decide

example : forms "a\u000bb\u000cc" newlineConfig =
    #["a", "\u000b", "b", "\u000c", "c"] := by
  native_decide

example : spans "a\r\nb\nc\rd\u2028e" newlineConfig =
    #[⟨0, 1⟩, ⟨1, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨5, 6⟩, ⟨6, 7⟩, ⟨7, 8⟩,
      ⟨8, 11⟩, ⟨11, 12⟩] := by
  native_decide

private def extendInputs (inputs : Array String) : Array String :=
  inputs.flatMap fun input ↦
    #[input ++ "a", input ++ "1", input ++ "'", input ++ "-", input ++ ".", input ++ " ",
      input ++ "😀", input ++ "\u0301"]

private def smallInputs : Array String :=
  extendInputs (extendInputs (extendInputs #[""]))

private def configs : Array Config :=
  #[{}, { mode := .whitespace }, { keepNewlines := true },
    { splitHyphenated := false, splitForwardSlash := false },
    { splitContractions := false, splitAssimilations := false }]

def exhaustiveStructuralCheck : Bool :=
  smallInputs.all fun input ↦ configs.all fun config ↦ (tokenize input config).isWF

example : exhaustiveStructuralCheck = true := by native_decide

private def cursorPrefix : Option (String × String) := do
  let (first, cursor) ← (Tokenizer.default.cursor "one two").next?
  let (second, _) ← cursor.next?
  some (first.original, second.original)

example : cursorPrefix = some ("one", "two") := by native_decide

end NlpTests.Tokenize.Scanner
