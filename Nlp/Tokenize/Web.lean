import Nlp.Tokenize.Types

/-!
# Source-preserving web-token recognition

This module recognizes a deliberately conservative subset of common web tokens before the
generic English scanner runs. URLs require a case-insensitive `http://`, `https://`, `ftp://`, or
`www.` prefix and an ASCII authority. Their paths, queries, and fragments retain non-control
Unicode scalars. Email addresses use an ASCII local part and a dotted ASCII domain whose final
label contains at least two letters. Handles and hashtags use ASCII bodies, while their markers
may use ASCII or fullwidth forms. Complete Unicode hashtag categories remain a separate generated
data-table feature rather than an ad hoc range list.

Every recognizer advances through `String.Pos` values without extracting a candidate substring.
URL punctuation remains available inside paths, queries, and fragments, while a last-accepting
position removes terminal prose punctuation in the same pass. No recognizer crosses whitespace
or a logical line break because those characters are outside every accepted alphabet.
-/

namespace Nlp.Tokenize.Web

/-- The specialized lexical class of one recognized web token. -/
inductive Kind where
  | url
  | email
  | handle
  | hashtag
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace Kind

/-- Project a web-token class into the tokenizer's public coarse classification. -/
@[inline] def tokenKind : Kind → TokenKind
  | .url => .url
  | .email => .email
  | .handle => .handle
  | .hashtag => .hashtag

end Kind

/-- A nonempty web-token match tied to its exact source string and starting position. -/
structure Match (text : String) (start : text.Pos) where
  private mk ::
  stop : text.Pos
  nonempty : start < stop
  kind : Kind

@[inline] private def isAsciiUpper (character : Char) : Bool :=
  let code := character.toNat
  0x41 ≤ code && code ≤ 0x5A

@[inline] private def isAsciiLower (character : Char) : Bool :=
  let code := character.toNat
  0x61 ≤ code && code ≤ 0x7A

@[inline] private def isAsciiAlpha (character : Char) : Bool :=
  isAsciiUpper character || isAsciiLower character

@[inline] private def isAsciiDigit (character : Char) : Bool :=
  let code := character.toNat
  0x30 ≤ code && code ≤ 0x39

@[inline] private def isAsciiAlnum (character : Char) : Bool :=
  isAsciiAlpha character || isAsciiDigit character

@[inline] private def asciiCaselessEq (actual expectedLower : Char) : Bool :=
  actual == expectedLower ||
    (isAsciiUpper actual && actual.toNat + 0x20 == expectedLower.toNat)

private def consumeAsciiPrefix? (text : String) : List Char → text.Pos → Option text.Pos
  | [], position => some position
  | expected :: remaining, position =>
      if atEnd : position = text.endPos then
        none
      else if asciiCaselessEq (position.get atEnd) expected then
        consumeAsciiPrefix? text remaining (position.next atEnd)
      else
        none

private def urlBodyStart? (text : String) (start : text.Pos) : Option text.Pos :=
  (consumeAsciiPrefix? text ['h', 't', 't', 'p', 's', ':', '/', '/'] start).orElse fun _ ↦
    (consumeAsciiPrefix? text ['h', 't', 't', 'p', ':', '/', '/'] start).orElse fun _ ↦
      (consumeAsciiPrefix? text ['f', 't', 'p', ':', '/', '/'] start).orElse fun _ ↦
        consumeAsciiPrefix? text ['w', 'w', 'w', '.'] start

@[inline] private def isWebWhitespace (character : Char) : Bool :=
  let code := character.toNat
  character.isWhitespace || code == 0x000B || code == 0x000C || code == 0x0085 ||
    code == 0x00A0 || code == 0x1680 || (0x2000 ≤ code && code ≤ 0x200A) ||
    code == 0x2028 || code == 0x2029 || code == 0x202F || code == 0x205F ||
    code == 0x3000

@[inline] private def isControl (character : Char) : Bool :=
  let code := character.toNat
  code < 0x20 || (0x7F ≤ code && code ≤ 0x9F)

@[inline] private def isUrlAsciiCharacter (character : Char) : Bool :=
  isAsciiAlnum character ||
    match character with
    | '-' | '.' | '_' | '~' | ':' | '/' | '?' | '#' | '[' | ']' | '@' | '!'
    | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '=' | '%' => true
    | _ => false

@[inline] private def isUrlAuthorityCharacter (character : Char) : Bool :=
  isAsciiAlnum character ||
    match character with
    | '-' | '.' | '_' | '~' | ':' | '@' | '[' | ']' => true
    | _ => false

@[inline] private def isUrlTailCharacter (character : Char) : Bool :=
  if character.toNat < 0x80 then
    isUrlAsciiCharacter character
  else
    !isWebWhitespace character && !isControl character

@[inline] private def isUrlProseTerminal (character : Char) : Bool :=
  match character with
  | '.' | ',' | ';' | ':' | '!' | '?' | '\'' => true
  | _ =>
      match character.toNat with
      | 0x00BB  -- right-pointing double angle quotation mark
      | 0x2019  -- right single quotation mark
      | 0x201D  -- right double quotation mark
      | 0x2026  -- horizontal ellipsis
      | 0x203A  -- right-pointing single angle quotation mark
      | 0x3002  -- ideographic full stop
      | 0xFF01  -- fullwidth exclamation mark
      | 0xFF0E  -- fullwidth full stop
      | 0xFF1F  -- fullwidth question mark
        => true
      | _ => false

@[inline] private def startsUrlTail (character : Char) : Bool :=
  character == '/' || character == '?' || character == '#'

private structure UrlScanState (text : String) where
  accepted : Option text.Pos := none
  /-- `false` records `(` and `true` records `[` in exact nesting order. -/
  groups : Array Bool := #[]
  tail : Bool := false

@[inline] private def UrlScanState.acceptIfBalanced (state : UrlScanState text)
    (next : text.Pos) : UrlScanState text :=
  if state.groups.isEmpty then
    { state with accepted := some next }
  else
    state

@[inline] private def UrlScanState.step (state : UrlScanState text) (character : Char)
    (next : text.Pos) : UrlScanState text :=
  let state := if startsUrlTail character then { state with tail := true } else state
  match character with
  | '(' => { state with groups := state.groups.push false }
  | ')' =>
      if state.groups.back? == some false then
        ({ state with groups := state.groups.pop }).acceptIfBalanced next
      else
        state
  | '[' => { state with groups := state.groups.push true }
  | ']' =>
      if state.groups.back? == some true then
        ({ state with groups := state.groups.pop }).acceptIfBalanced next
      else
        state
  | _ => if isUrlProseTerminal character then state else state.acceptIfBalanced next

private def urlStop? (text : String) (start : text.Pos) : Option text.Pos := Id.run do
  let some bodyStart := urlBodyStart? text start | return none
  if hasBody : bodyStart ≠ text.endPos then
    let first := bodyStart.get hasBody
    if !isAsciiAlnum first then
      return none
    let firstStop := bodyStart.next hasBody
    let mut position := firstStop
    let mut state : UrlScanState text := { accepted := some firstStop }
    for _ in [0:text.utf8ByteSize + 1] do
      if hasCharacter : position ≠ text.endPos then
        let character := position.get hasCharacter
        let allowed :=
          if state.tail then isUrlTailCharacter character
          else isUrlAuthorityCharacter character || startsUrlTail character
        if !allowed then
          return state.accepted
        let next := position.next hasCharacter
        state := state.step character next
        position := next
      else
        return state.accepted
    return state.accepted
  else
    return none

private inductive EmailPhase where
  | local (length : Nat) (lastWasDot : Bool)
  | domain (dots labelLength : Nat) (lastWasHyphen allLetters : Bool)

@[inline] private def isEmailLocalPlain (character : Char) : Bool :=
  isAsciiAlnum character ||
    match character with
    | '_' | '%' | '+' | '-' => true
    | _ => false

private def emailStop? (text : String) (start : text.Pos) : Option text.Pos := Id.run do
  let mut position := start
  let mut phase : EmailPhase := .local 0 false
  let mut accepted : Option text.Pos := none
  for _ in [0:text.utf8ByteSize + 1] do
    if hasCharacter : position ≠ text.endPos then
      let character := position.get hasCharacter
      let next := position.next hasCharacter
      match phase with
      | .local length lastWasDot =>
          if isEmailLocalPlain character then
            phase := .local (length + 1) false
          else if character == '.' && 0 < length && !lastWasDot then
            phase := .local (length + 1) true
          else if character == '@' && 0 < length && !lastWasDot then
            phase := .domain 0 0 false true
          else
            return accepted
      | .domain dots labelLength lastWasHyphen allLetters =>
          if isAsciiAlnum character then
            let nextLength := labelLength + 1
            let nextAllLetters := allLetters && isAsciiAlpha character
            phase := .domain dots nextLength false nextAllLetters
            accepted := none
            if 0 < dots && 2 ≤ nextLength && nextAllLetters then
              accepted := some next
          else if character == '-' && 0 < labelLength then
            phase := .domain dots (labelLength + 1) true false
            accepted := none
          else if character == '.' && 0 < labelLength && !lastWasHyphen then
            phase := .domain (dots + 1) 0 false true
          else
            return accepted
      position := next
    else
      return accepted
  return accepted

private def prefixedStop? (text : String) (start : text.Pos) (marker : Char → Bool)
    (firstAllowed restAllowed terminal : Char → Bool) : Option text.Pos := Id.run do
  if hasMarker : start ≠ text.endPos then
    if !marker (start.get hasMarker) then
      return none
    let firstPosition := start.next hasMarker
    if hasBody : firstPosition ≠ text.endPos then
      let first := firstPosition.get hasBody
      if !firstAllowed first then
        return none
      let firstStop := firstPosition.next hasBody
      let mut position := firstStop
      let mut accepted := if terminal first then some firstStop else none
      for _ in [0:text.utf8ByteSize + 1] do
        if hasCharacter : position ≠ text.endPos then
          let character := position.get hasCharacter
          if !restAllowed character then
            return accepted
          let next := position.next hasCharacter
          if terminal character then
            accepted := some next
          position := next
        else
          return accepted
      return accepted
    else
      return none
  else
    return none

@[inline] private def isHandleFirst (character : Char) : Bool :=
  isAsciiAlpha character || character == '_'

@[inline] private def isHandleRest (character : Char) : Bool :=
  isAsciiAlnum character || character == '_'

@[inline] private def isHashtagFirst (character : Char) : Bool :=
  isAsciiAlpha character

@[inline] private def isHashtagRest (character : Char) : Bool :=
  isAsciiAlnum character || character == '_'

@[inline] private def isHashtagTerminal (character : Char) : Bool :=
  isAsciiAlnum character

@[inline] private def isHandleMarker (character : Char) : Bool :=
  character == '@' || character.toNat == 0xFF20

@[inline] private def isHashtagMarker (character : Char) : Bool :=
  character == '#' || character.toNat == 0xFF03

private def handleStop? (text : String) (start : text.Pos) : Option text.Pos :=
  prefixedStop? text start isHandleMarker isHandleFirst isHandleRest isHandleRest

private def hashtagStop? (text : String) (start : text.Pos) : Option text.Pos :=
  prefixedStop? text start isHashtagMarker isHashtagFirst isHashtagRest isHashtagTerminal

@[inline] private def ofStop? (text : String) (start : text.Pos) (kind : Kind)
    (stop? : Option text.Pos) : Option (Match text start) := do
  let stop ← stop?
  if nonempty : start < stop then some ⟨stop, nonempty, kind⟩ else none

private def preferLongest (preferred alternative : Option (Match text start)) :
    Option (Match text start) :=
  match preferred, alternative with
  | none, result | result, none => result
  | some first, some second => if first.stop < second.stop then some second else some first

/--
Recognize the longest enabled web token at `start`.

Strictly longer matches win; equal endpoints retain the stable priority URL, email, handle, then
hashtag. The result refers only to positions in `text` and never materializes the matched source.
-/
def match? (config : WebConfig) (text : String) (start : text.Pos) :
    Option (Match text start) :=
  let url :=
    if config.recognizeUrls then ofStop? text start .url (urlStop? text start) else none
  let email :=
    if config.recognizeEmails then ofStop? text start .email (emailStop? text start) else none
  let handle :=
    if config.recognizeHandles then ofStop? text start .handle (handleStop? text start) else none
  let hashtag :=
    if config.recognizeHashtags then
      ofStop? text start .hashtag (hashtagStop? text start)
    else
      none
  preferLongest (preferLongest (preferLongest url email) handle) hashtag

end Nlp.Tokenize.Web
