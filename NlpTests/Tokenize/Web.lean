import Nlp.Tokenize.Web

namespace NlpTests.Tokenize.Web

open Nlp.Tokenize

private def result? (text : String) (config : WebConfig := {}) : Option (String × Web.Kind) :=
  (Web.match? config text text.startPos).map fun found ↦
    (text.extract text.startPos found.stop, found.kind)

example : result? "https://example.com/a(b)?q=x+y#frag)." =
    some ("https://example.com/a(b)?q=x+y#frag", .url) := by
  native_decide

example : result? "HTTPS://EXAMPLE.COM/path" = some ("HTTPS://EXAMPLE.COM/path", .url) := by
  native_decide

example : result? "ftp://host/path/" = some ("ftp://host/path/", .url) := by
  native_decide

example : result? "https://example.test/a,b;c:d?q=one&x=two" =
    some ("https://example.test/a,b;c:d?q=one&x=two", .url) := by
  native_decide

example : result? "https://example.test/猫?q=犬&" =
    some ("https://example.test/猫?q=犬&", .url) := by
  native_decide

example : result? "https://example.test/path?q=#frag@" =
    some ("https://example.test/path?q=#frag@", .url) := by
  native_decide

example : result? "https://example.test/ok(foo" =
    some ("https://example.test/ok", .url) := by
  native_decide

example : result? "https://example.test/ok(a[b]c)" =
    some ("https://example.test/ok(a[b]c)", .url) := by
  native_decide

example : result? "https://example.test/ok(a[b)c" =
    some ("https://example.test/ok", .url) := by
  native_decide

example : result? "https://example.test/ok([a)]b" =
    some ("https://example.test/ok", .url) := by
  native_decide

example : result? "https://example.test/x y" = some ("https://example.test/x", .url) := by
  native_decide

example : result? "https://example.test/x\ny" = some ("https://example.test/x", .url) := by
  native_decide

example : result? "http://" = none := by native_decide
example : result? "http://-host.test" = none := by native_decide
example : result? "WWW.example.com/path)." = some ("WWW.example.com/path", .url) := by
  native_decide

example : result? "example.com" = none := by native_decide

example : result? "a+b@example.co.uk," = some ("a+b@example.co.uk", .email) := by
  native_decide

example : result? "first.last@sub.example.com." =
    some ("first.last@sub.example.com", .email) := by
  native_decide

example : result? "a..b@example.com" = none := by native_decide
example : result? "a@example.c" = none := by native_decide
example : result? "a@-example.com" = none := by native_decide
example : result? "a@example.com2" = none := by native_decide
example : result? "a@example.com-" = none := by native_decide
example : result? "a@example.com. next" = some ("a@example.com", .email) := by
  native_decide

example : result? "@lean_4!" = some ("@lean_4", .handle) := by native_decide
example : result? "@9lean" = none := by native_decide
example : result? "#Lean4_rocks," = some ("#Lean4_rocks", .hashtag) := by native_decide
example : result? "#Lean_" = some ("#Lean", .hashtag) := by native_decide
example : result? "#形式化_验证!" = none := by native_decide
example : result? "＃lean2!" = some ("＃lean2", .hashtag) := by native_decide
example : result? "＠lean_4!" = some ("＠lean_4", .handle) := by native_decide
example : result? "#123" = none := by native_decide

example : result? "https://example.com" { recognizeUrls := false } = none := by
  native_decide

example : result? "a@example.com" { recognizeEmails := false } = none := by
  native_decide

example : result? "@lean" { recognizeHandles := false } = none := by native_decide
example : result? "#lean" { recognizeHashtags := false } = none := by native_decide

private def longUrl : String :=
  "https://a.test/" ++ String.join (List.replicate 4096 "a") ++ ")."

example : (result? longUrl).map (fun result ↦ result.1.utf8ByteSize) = some 4111 := by
  native_decide

private def longMalformedEmail : String :=
  String.join (List.replicate 4096 "a") ++ "@host.x"

example : result? longMalformedEmail = none := by native_decide

@[inline] private def referenceAsciiAlpha (character : Char) : Bool :=
  ('A' ≤ character && character ≤ 'Z') || ('a' ≤ character && character ≤ 'z')

@[inline] private def referenceAsciiDigit (character : Char) : Bool :=
  '0' ≤ character && character ≤ '9'

@[inline] private def referenceHandleRest (character : Char) : Bool :=
  referenceAsciiAlpha character || referenceAsciiDigit character || character == '_'

@[inline] private def referenceEmailLocalCharacter (character : Char) : Bool :=
  referenceHandleRest character ||
    match character with
    | '.' | '%' | '+' | '-' => true
    | _ => false

@[inline] private def referenceEmailCandidateCharacter (character : Char) : Bool :=
  referenceEmailLocalCharacter character || character == '@'

private def referenceNoAdjacentDots : List Char → Bool
  | [] | [_] => true
  | left :: right :: remaining =>
      !(left == '.' && right == '.') && referenceNoAdjacentDots (right :: remaining)

private def referenceValidLocal (localPart : List Char) : Bool :=
  !localPart.isEmpty && localPart.all referenceEmailLocalCharacter &&
    referenceNoAdjacentDots localPart && localPart[0]? != some '.' &&
    localPart.getLast? != some '.'

private def referenceValidDomainLabel (label : List Char) : Bool :=
  !label.isEmpty && label.all (fun character ↦
    referenceAsciiAlpha character || referenceAsciiDigit character || character == '-') &&
    label[0]?.any (fun character ↦ referenceAsciiAlpha character ||
      referenceAsciiDigit character) &&
    label.getLast?.any (fun character ↦ referenceAsciiAlpha character ||
      referenceAsciiDigit character)

private def referenceValidEmail (characters : List Char) : Bool :=
  match characters.splitOn '@' with
  | [localPart, domain] =>
      let labels := domain.splitOn '.'
      referenceValidLocal localPart && 2 ≤ labels.length &&
        labels.all referenceValidDomainLabel && labels.getLast?.any fun finalLabel ↦
            2 ≤ finalLabel.length && finalLabel.all referenceAsciiAlpha
  | _ => false

private def referenceEmail? (text : String) : Option (Nat × Web.Kind) :=
  let candidate := text.toList.takeWhile referenceEmailCandidateCharacter
  let withoutProseDots := (candidate.reverse.dropWhile (· == '.')).reverse
  if referenceValidEmail withoutProseDots then some (withoutProseDots.length, .email) else none

private def emailActual? (text : String) : Option (Nat × Web.Kind) :=
  let config : WebConfig := {
    recognizeUrls := false
    recognizeHandles := false
    recognizeHashtags := false
  }
  (Web.match? config text text.startPos).map fun found ↦
    (found.stop.offset.byteIdx, found.kind)

private def referenceRest (allowed terminal : Char → Bool) :
    List Char → Nat → Nat → Nat
  | [], _, accepted => accepted
  | character :: remaining, consumed, accepted =>
      if allowed character then
        let next := consumed + 1
        referenceRest allowed terminal remaining next
          (if terminal character then next else accepted)
      else
        accepted

private def referenceSocial? (text : String) : Option (Nat × Web.Kind) :=
  match text.toList with
  | '@' :: first :: remaining =>
      if referenceAsciiAlpha first || first == '_' then
        some (referenceRest referenceHandleRest referenceHandleRest remaining 2 2, .handle)
      else
        none
  | '#' :: first :: remaining =>
      if referenceAsciiAlpha first then
        some (referenceRest referenceHandleRest
          (fun character ↦ referenceAsciiAlpha character || referenceAsciiDigit character)
          remaining 2 2, .hashtag)
      else
        none
  | _ => none

private def socialActual? (text : String) : Option (Nat × Web.Kind) :=
  let config : WebConfig := { recognizeUrls := false, recognizeEmails := false }
  (Web.match? config text text.startPos).map fun found ↦
    (found.stop.offset.byteIdx, found.kind)

private def extendInputs (inputs : Array String) : Array String :=
  inputs.flatMap fun input ↦
    #[input ++ "@", input ++ "#", input ++ "a", input ++ "1", input ++ "_",
      input ++ "!"]

private def socialInputs : Array String :=
  let one := extendInputs #[""]
  let two := extendInputs one
  let three := extendInputs two
  let four := extendInputs three
  #[""] ++ one ++ two ++ three ++ four

/-- Exhaustively compare the position scanner with a separate list specification. -/
def exhaustiveSocialReference : Bool :=
  socialInputs.all fun input ↦ socialActual? input == referenceSocial? input

example : exhaustiveSocialReference = true := by native_decide

private def extendEmailInputs (inputs : Array String) : Array String :=
  inputs.flatMap fun input ↦
    #[input ++ "a", input ++ "b", input ++ "2", input ++ "@", input ++ ".",
      input ++ "-", input ++ "!"]

private def emailInputs : Array String :=
  let one := extendEmailInputs #[""]
  let two := extendEmailInputs one
  let three := extendEmailInputs two
  let four := extendEmailInputs three
  let five := extendEmailInputs four
  let six := extendEmailInputs five
  #[""] ++ one ++ two ++ three ++ four ++ five ++ six

/-- Exhaustively compare ASCII email recognition with a declarative list specification. -/
def exhaustiveEmailReference : Bool :=
  emailInputs.all fun input ↦ emailActual? input == referenceEmail? input

example : exhaustiveEmailReference = true := by native_decide

end NlpTests.Tokenize.Web
