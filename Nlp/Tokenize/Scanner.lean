import Nlp.Tokenize.Types

/-!
# Streaming rule tokenizer

This module implements a dependency-free tokenizer over `String.Pos`. The scanner never converts
the source to a character list: it advances through Unicode scalar values while retaining UTF-8
byte positions, and it uses an ASCII-first classifier for the common English path. Maximal source
runs stay as positions; only short split candidates are temporarily sliced, and emitted forms are
materialized on demand.

The English/UD-oriented mode implements a deliberately explicit core rather than copying Stanford
CoreNLP's GPL tokenizer tables. It recognizes words from all scripts, decimal-like numbers, common
punctuation runs, Unicode whitespace, CRLF as one logical newline, productive English apostrophe
contractions, and the documented treebank assimilation set. URLs, email addresses, SGML, phone
numbers, mixed fractions, abbreviation lexicons, and language-specific multi-word-token models
remain separate layers.
-/

namespace Nlp.Tokenize

namespace Scanner

/-- Unicode White_Space code points not covered by Lean's four-character `Char.isWhitespace`. -/
@[inline] def isWhitespace (character : Char) : Bool :=
  let code := character.toNat
  character.isWhitespace || code == 0x000B || code == 0x000C || code == 0x0085 ||
    code == 0x00A0 || code == 0x1680 || (0x2000 ≤ code && code ≤ 0x200A) ||
    code == 0x2028 || code == 0x2029 || code == 0x202F || code == 0x205F ||
    code == 0x3000

/-- Unicode scalar values treated as logical line breaks. -/
@[inline] def isLineBreak (character : Char) : Bool :=
  character == '\n' || character == '\r' || character.toNat == 0x000B ||
    character.toNat == 0x000C || character.toNat == 0x0085 ||
    character.toNat == 0x2028 || character.toNat == 0x2029

@[inline] private def isAscii (character : Char) : Bool := character.toNat < 0x80

@[inline] private def inCodeRange (code lower upper : Nat) : Bool :=
  lower ≤ code && code ≤ upper

/-- Unicode 17 `General_Category=Decimal_Number` code-point ranges. -/
def isDecimalDigit (character : Char) : Bool :=
  let code := character.toNat
  if character.isDigit then
    true
  else if code < 0x0660 then
    false
  else if code < 0x2000 then
    inCodeRange code 0x0660 0x0669 || inCodeRange code 0x06F0 0x06F9 ||
      inCodeRange code 0x07C0 0x07C9 || inCodeRange code 0x0966 0x096F ||
      inCodeRange code 0x09E6 0x09EF || inCodeRange code 0x0A66 0x0A6F ||
      inCodeRange code 0x0AE6 0x0AEF || inCodeRange code 0x0B66 0x0B6F ||
      inCodeRange code 0x0BE6 0x0BEF || inCodeRange code 0x0C66 0x0C6F ||
      inCodeRange code 0x0CE6 0x0CEF || inCodeRange code 0x0D66 0x0D6F ||
      inCodeRange code 0x0DE6 0x0DEF || inCodeRange code 0x0E50 0x0E59 ||
      inCodeRange code 0x0ED0 0x0ED9 || inCodeRange code 0x0F20 0x0F29 ||
      inCodeRange code 0x1040 0x1049 || inCodeRange code 0x1090 0x1099 ||
      inCodeRange code 0x17E0 0x17E9 || inCodeRange code 0x1810 0x1819 ||
      inCodeRange code 0x1946 0x194F || inCodeRange code 0x19D0 0x19D9 ||
      inCodeRange code 0x1A80 0x1A89 || inCodeRange code 0x1A90 0x1A99 ||
      inCodeRange code 0x1B50 0x1B59 || inCodeRange code 0x1BB0 0x1BB9 ||
      inCodeRange code 0x1C40 0x1C49 || inCodeRange code 0x1C50 0x1C59
  else if code < 0xA620 then
    false
  else if code < 0x10000 then
    inCodeRange code 0xA620 0xA629 || inCodeRange code 0xA8D0 0xA8D9 ||
      inCodeRange code 0xA900 0xA909 || inCodeRange code 0xA9D0 0xA9D9 ||
      inCodeRange code 0xA9F0 0xA9F9 || inCodeRange code 0xAA50 0xAA59 ||
      inCodeRange code 0xABF0 0xABF9 || inCodeRange code 0xFF10 0xFF19
  else
    inCodeRange code 0x104A0 0x104A9 || inCodeRange code 0x10D30 0x10D39 ||
      inCodeRange code 0x10D40 0x10D49 ||
      inCodeRange code 0x11066 0x1106F || inCodeRange code 0x110F0 0x110F9 ||
      inCodeRange code 0x11136 0x1113F || inCodeRange code 0x111D0 0x111D9 ||
      inCodeRange code 0x112F0 0x112F9 || inCodeRange code 0x11450 0x11459 ||
      inCodeRange code 0x114D0 0x114D9 || inCodeRange code 0x11650 0x11659 ||
      inCodeRange code 0x116C0 0x116C9 || inCodeRange code 0x116D0 0x116E3 ||
      inCodeRange code 0x11730 0x11739 || inCodeRange code 0x118E0 0x118E9 ||
      inCodeRange code 0x11950 0x11959 || inCodeRange code 0x11BF0 0x11BF9 ||
      inCodeRange code 0x11C50 0x11C59 || inCodeRange code 0x11D50 0x11D59 ||
      inCodeRange code 0x11DA0 0x11DA9 || inCodeRange code 0x11DE0 0x11DE9 ||
      inCodeRange code 0x11F50 0x11F59 || inCodeRange code 0x16130 0x16139 ||
      inCodeRange code 0x16A60 0x16A69 || inCodeRange code 0x16AC0 0x16AC9 ||
      inCodeRange code 0x16B50 0x16B59 || inCodeRange code 0x16D70 0x16D79 ||
      inCodeRange code 0x1CCF0 0x1CCF9 || inCodeRange code 0x1D7CE 0x1D7FF ||
      inCodeRange code 0x1E140 0x1E149 || inCodeRange code 0x1E2F0 0x1E2F9 ||
      inCodeRange code 0x1E4F0 0x1E4F9 || inCodeRange code 0x1E5F1 0x1E5FA ||
      inCodeRange code 0x1E950 0x1E959 || inCodeRange code 0x1FBF0 0x1FBF9

@[inline] private def isAsciiWord (character : Char) : Bool :=
  character.isAlphanum || character == '_'

@[inline] private def isApostrophe (character : Char) : Bool :=
  character == '\'' || character.toNat == 0x2019

@[inline] private def isHyphen (character : Char) : Bool :=
  character == '-' || character.toNat == 0x2010 || character.toNat == 0x2011

@[inline] private def isSlash (character : Char) : Bool :=
  character == '/' || character.toNat == 0x2044

@[inline] private def isCombiningMark (character : Char) : Bool :=
  let code := character.toNat
  (0x0300 ≤ code && code ≤ 0x036F) || (0x1AB0 ≤ code && code ≤ 0x1AFF) ||
    (0x1DC0 ≤ code && code ≤ 0x1DFF) || (0x20D0 ≤ code && code ≤ 0x20FF) ||
    (0xFE20 ≤ code && code ≤ 0xFE2F)

@[inline] private def isUnicodePunctuation (character : Char) : Bool :=
  let code := character.toNat
  code == 0x00A1 || code == 0x00A7 || code == 0x00AB || code == 0x00B6 ||
    code == 0x00B7 || code == 0x00BB || code == 0x00BF ||
    inCodeRange code 0x055A 0x055F || inCodeRange code 0x0589 0x058A ||
    code == 0x05BE || code == 0x05C0 || code == 0x05C3 || code == 0x05C6 ||
    inCodeRange code 0x05F3 0x05F4 || inCodeRange code 0x0609 0x060A ||
    inCodeRange code 0x060C 0x060D || code == 0x061B ||
    inCodeRange code 0x061D 0x061F || inCodeRange code 0x066A 0x066D ||
    code == 0x06D4 || inCodeRange code 0x0964 0x0965 || code == 0x1362 ||
    code == 0x1803 || code == 0x1809 || inCodeRange code 0x2010 0x2027 ||
    inCodeRange code 0x2030 0x205E || inCodeRange code 0x2E00 0x2E7F ||
    inCodeRange code 0x3001 0x3003 || inCodeRange code 0x3008 0x3011 ||
    inCodeRange code 0x3014 0x301F || code == 0x3030 || code == 0x303D ||
    inCodeRange code 0xFE10 0xFE1F || inCodeRange code 0xFE30 0xFE61 ||
    code == 0xFE63 || code == 0xFE68 || inCodeRange code 0xFE6A 0xFE6B ||
    inCodeRange code 0xFF01 0xFF03 || inCodeRange code 0xFF05 0xFF0A ||
    inCodeRange code 0xFF0C 0xFF0F || inCodeRange code 0xFF1A 0xFF1B ||
    inCodeRange code 0xFF1F 0xFF20 || inCodeRange code 0xFF3B 0xFF3D ||
    code == 0xFF3F || code == 0xFF5B || code == 0xFF5D ||
    inCodeRange code 0xFF5F 0xFF65

@[inline] private def isUnicodeSymbol (character : Char) : Bool :=
  let code := character.toNat
  inCodeRange code 0x00A2 0x00A6 || code == 0x00A8 || code == 0x00A9 ||
    code == 0x00AC || inCodeRange code 0x00AE 0x00B1 || code == 0x00B4 ||
    code == 0x00B8 || code == 0x00D7 || code == 0x00F7 ||
    inCodeRange code 0x20A0 0x20C1 || code == 0x2116 || code == 0x2117 ||
    inCodeRange code 0x2120 0x2122 || inCodeRange code 0x2190 0x2BFF ||
    code == 0x3004 || inCodeRange code 0x3012 0x3013 || code == 0x3020 ||
    inCodeRange code 0x3036 0x3037 || inCodeRange code 0x303E 0x303F ||
    code == 0xFDFC || code == 0xFE62 || inCodeRange code 0xFE64 0xFE66 ||
    code == 0xFE69 || code == 0xFF04 || code == 0xFF0B ||
    inCodeRange code 0xFF1C 0xFF1E || code == 0xFF3E || code == 0xFF40 ||
    code == 0xFF5C || code == 0xFF5E || inCodeRange code 0xFFE0 0xFFE6 ||
    inCodeRange code 0x1F000 0x1FAFF

@[inline] private def isAsciiPunctuation (character : Char) : Bool :=
  match character with
  | '.' | ',' | ';' | ':' | '!' | '?' | '(' | ')' | '[' | ']' | '{' | '}'
  | '<' | '>' | '"' | '\'' | '`' | '-' | '/' | '\\' => true
  | _ => false

@[inline] private def isAsciiSymbol (character : Char) : Bool :=
  match character with
  | '#' | '$' | '%' | '&' | '*' | '+' | '=' | '@' | '^' | '|' | '~' => true
  | _ => false

@[inline] private def isPunctuation (character : Char) : Bool :=
  if isAscii character then isAsciiPunctuation character else isUnicodePunctuation character

@[inline] private def isSymbol (character : Char) : Bool :=
  if isAscii character then isAsciiSymbol character else isUnicodeSymbol character

/-- Non-ASCII values not known to be whitespace, punctuation, or symbols remain word scalars. -/
@[inline] private def isWordScalar (character : Char) : Bool :=
  if isAscii character then
    isAsciiWord character
  else
    isCombiningMark character ||
      (!isWhitespace character && !isUnicodePunctuation character && !isUnicodeSymbol character)

@[inline] private def charAt? (text : String) (position : text.Pos) : Option Char :=
  if atEnd : position = text.endPos then none else some (position.get atEnd)

@[inline] private def charAfter? (text : String) (position : text.Pos) : Option Char :=
  if atEnd : position = text.endPos then
    none
  else
    charAt? text (position.next atEnd)

/-- A scanned end known to lie strictly after its token start. -/
private structure EndAfter (text : String) (start : text.Pos) where
  position : text.Pos
  after : start < position

namespace EndAfter

@[inline] private def first (start : text.Pos) (notAtEnd : start ≠ text.endPos) :
    EndAfter text start :=
  ⟨start.next notAtEnd, String.Pos.lt_next⟩

@[inline] private def next (stop : EndAfter text start)
    (notAtEnd : stop.position ≠ text.endPos) : EndAfter text start :=
  ⟨stop.position.next notAtEnd, String.Pos.lt_trans stop.after String.Pos.lt_next⟩

end EndAfter

/-- Consume a maximal run after an already accepted first scalar. -/
private def takeRest (text : String) (start : text.Pos) (notAtEnd : start ≠ text.endPos)
    (accept : text.Pos → Char → Bool) : EndAfter text start := Id.run do
  let mut stop := EndAfter.first start notAtEnd
  for _ in [0:text.utf8ByteSize] do
    if hasCharacter : stop.position ≠ text.endPos then
      let character := stop.position.get hasCharacter
      if accept stop.position character then
        stop := stop.next hasCharacter
      else
        return stop
    else
      return stop
  return stop

@[inline] private def nextIsWord (text : String) (position : text.Pos) : Bool :=
  (charAfter? text position).any isWordScalar

@[inline] private def nextIsDigit (text : String) (position : text.Pos) : Bool :=
  (charAfter? text position).any isDecimalDigit

/-- Recognize the final dot in an initialism such as `U.S.` without joining ordinary final dots. -/
private def isAcronymFinalPeriod (text : String) (position : text.Pos) : Bool :=
  if hasPrevious : position ≠ text.startPos then
    let previous := position.prev hasPrevious
    if previous.get!.isAlpha then
      if hasSeparator : previous ≠ text.startPos then
        let separator := previous.prev hasSeparator
        if separator.get! == '.' then
          if hasLetter : separator ≠ text.startPos then
            (separator.prev hasLetter).get!.isAlpha
          else
            false
        else
          false
      else
        false
    else
      false
  else
    false

@[inline] private def wordContinues (config : Config) (text : String)
    (position : text.Pos) (character : Char) : Bool :=
  isWordScalar character ||
    (isApostrophe character && nextIsWord text position) ||
    (isHyphen character && !config.splitHyphenated && nextIsWord text position) ||
    (isSlash character && !config.splitForwardSlash && nextIsWord text position) ||
    (character == '.' &&
      ((charAfter? text position).any Char.isAlpha || isAcronymFinalPeriod text position))

@[inline] private def numberContinues (config : Config) (text : String)
    (position : text.Pos) (character : Char) : Bool :=
  isWordScalar character ||
    ((character == '.' || character == ',' || character == ':') && nextIsDigit text position) ||
    (isSlash character && !config.splitForwardSlash && nextIsDigit text position) ||
    (isHyphen character && !config.splitHyphenated && nextIsDigit text position)

@[inline] private def punctuationContinues (first current : Char) : Bool :=
  ((first == '!' || first == '?') && (current == '!' || current == '?')) ||
    (first == '.' && current == '.') || (isHyphen first && isHyphen current)

@[inline] private def symbolContinues (character : Char) : Bool :=
  isSymbol character || character.toNat == 0x200D || character.toNat == 0xFE0F ||
    (0x1F3FB ≤ character.toNat && character.toNat ≤ 0x1F3FF)

private def newlineEnd (text : String) (start : text.Pos) (notAtEnd : start ≠ text.endPos)
    (character : Char) : EndAfter text start :=
  let first := EndAfter.first start notAtEnd
  if character == '\r' then
    if firstAtEnd : first.position = text.endPos then
      first
    else if first.position.get firstAtEnd == '\n' then
      first.next firstAtEnd
    else
      first
  else
    first

/-- Advance by exactly `count` Unicode scalar values, failing at the source end. -/
private def advanceScalars? (text : String) (position : text.Pos) : Nat → Option text.Pos
  | 0 => some position
  | count + 1 =>
      if atEnd : position = text.endPos then
        none
      else
        advanceScalars? text (position.next atEnd) count

@[inline] private def suffixPrefix? (word suffix : String) : Option Nat :=
  if suffix.length < word.length && word.endsWith suffix then
    some (word.length - suffix.length)
  else
    none

private def assimilationPrefix? : String → Option Nat
  | "cannot" => some 3
  | "gonna" => some 3
  | "wanna" => some 3
  | "gotta" => some 3
  | "lemme" => some 3
  | "gimme" => some 3
  | "d'ye" => some 2
  | "d’ye" => some 2
  | _ => none

private def contractionPrefix? (word : String) : Option Nat :=
  if word == "'tis" || word == "’tis" || word == "'twas" || word == "’twas" then
    some 2
  else
    (suffixPrefix? word "n't").orElse fun _ ↦
      (suffixPrefix? word "n’t").orElse fun _ ↦
        (suffixPrefix? word "'ll").orElse fun _ ↦
          (suffixPrefix? word "’ll").orElse fun _ ↦
            (suffixPrefix? word "'re").orElse fun _ ↦
              (suffixPrefix? word "’re").orElse fun _ ↦
                (suffixPrefix? word "'ve").orElse fun _ ↦
                  (suffixPrefix? word "’ve").orElse fun _ ↦
                    (suffixPrefix? word "'s").orElse fun _ ↦
                      (suffixPrefix? word "’s").orElse fun _ ↦
                        (suffixPrefix? word "'m").orElse fun _ ↦
                          (suffixPrefix? word "’m").orElse fun _ ↦
                            (suffixPrefix? word "'d").orElse fun _ ↦
                              (suffixPrefix? word "’d")

private def splitAt? (text : String) (start stop : text.Pos)
    (prefixScalars : Nat) : Option (Token text × Token text) := do
  let middle ← advanceScalars? text start prefixScalars
  if left : start < middle then
    if right : middle < stop then
      some (Token.ofPositions start middle left .word,
        Token.ofPositions middle stop right .word)
    else
      none
  else
    none

/-- Split at two absolute scalar offsets, producing three adjacent nonempty source pieces. -/
private def splitAtTwo? (text : String) (start stop : text.Pos)
    (firstScalars secondScalars : Nat) : Option (List (Token text)) := do
  let first ← advanceScalars? text start firstScalars
  let second ← advanceScalars? text start secondScalars
  if firstAfterStart : start < first then
    if secondAfterFirst : first < second then
      if stopAfterSecond : second < stop then
        some [Token.ofPositions start first firstAfterStart .word,
          Token.ofPositions first second secondAfterFirst .word,
          Token.ofPositions second stop stopAfterSecond .word]
      else
        none
    else
      none
  else
    none

private def PiecesWF (lower upper : text.Pos) (pieces : List (Token text)) : Prop :=
  Tokenization.ordered pieces = true ∧
    ∀ token ∈ pieces, lower ≤ token.startPos ∧ token.endPos ≤ upper

private theorem PiecesWF.lower_mono {lower lower' upper : text.Pos}
    {pieces : List (Token text)} (before : lower' ≤ lower)
    (wellFormed : PiecesWF lower upper pieces) : PiecesWF lower' upper pieces := by
  refine ⟨wellFormed.1, fun token member ↦ ?_⟩
  exact ⟨Std.le_trans before (wellFormed.2 token member).1, (wellFormed.2 token member).2⟩

private theorem splitAt?_piecesWF (text : String) (start stop : text.Pos)
    (prefixScalars : Nat) :
    match splitAt? text start stop prefixScalars with
    | none => True
    | some (left, right) => PiecesWF start stop [left, right] := by
  generalize middleResult : advanceScalars? text start prefixScalars = result
  cases result with
  | none => simp [splitAt?, middleResult]
  | some middle =>
      by_cases left : start < middle
      · by_cases right : middle < stop
        · simp [splitAt?, middleResult, left, right, PiecesWF, Tokenization.ordered,
            Token.ofPositions]
          exact ⟨Std.le_of_lt right, Std.le_of_lt left⟩
        · simp [splitAt?, middleResult, left, right]
      · simp [splitAt?, middleResult, left]

private theorem splitAtTwo?_piecesWF (text : String) (start stop : text.Pos)
    (firstScalars secondScalars : Nat) :
    match splitAtTwo? text start stop firstScalars secondScalars with
    | none => True
    | some pieces => PiecesWF start stop pieces := by
  generalize firstResult : advanceScalars? text start firstScalars = first?
  generalize secondResult : advanceScalars? text start secondScalars = second?
  cases first? with
  | none => simp [splitAtTwo?, firstResult]
  | some first =>
      cases second? with
      | none => simp [splitAtTwo?, firstResult, secondResult]
      | some second =>
          by_cases firstAfterStart : start < first
          · by_cases secondAfterFirst : first < second
            · by_cases stopAfterSecond : second < stop
              · simp [splitAtTwo?, firstResult, secondResult, firstAfterStart,
                  secondAfterFirst, stopAfterSecond, PiecesWF, Tokenization.ordered,
                  Token.ofPositions]
                exact ⟨Std.le_trans (Std.le_of_lt secondAfterFirst) (Std.le_of_lt stopAfterSecond),
                  ⟨⟨Std.le_of_lt firstAfterStart, Std.le_of_lt stopAfterSecond⟩,
                    Std.le_trans (Std.le_of_lt firstAfterStart) (Std.le_of_lt secondAfterFirst)⟩⟩
              · simp_all [splitAtTwo?]
            · simp_all [splitAtTwo?]
          · simp [splitAtTwo?, firstResult, secondResult, firstAfterStart]

@[inline] private def couldContract (text : String) (start stop : text.Pos) : Bool :=
  let last := (stop.prevn 1).get!
  let penultimate := (stop.prevn 2).get!
  let antepenultimate := (stop.prevn 3).get!
  (isApostrophe (start.get!) && (last == 's' || last == 'e')) ||
    ((last == 's' || last == 'm' || last == 'd' || last == 't') &&
      isApostrophe penultimate) ||
    ((last == 'e' || last == 'l') && isApostrophe antepenultimate)

@[inline] private def couldAssimilate (text : String) (start stop : text.Pos) : Bool :=
  let width := stop.offset.byteIdx - start.offset.byteIdx
  let first := start.get!
  let second := charAfter? text start
  let last := (stop.prevn 1).get!
  let ca := (first == 'c' || first == 'C') &&
    (second == some 'a' || second == some 'A') && (last == 't' || last == 'T')
  let go := (first == 'g' || first == 'G') &&
    (second == some 'o' || second == some 'O') && (last == 'a' || last == 'A')
  let gi := (first == 'g' || first == 'G') &&
    (second == some 'i' || second == some 'I') && (last == 'e' || last == 'E')
  let wa := (first == 'w' || first == 'W') &&
    (second == some 'a' || second == some 'A') && (last == 'a' || last == 'A')
  let le := (first == 'l' || first == 'L') &&
    (second == some 'e' || second == some 'E') && (last == 'e' || last == 'E')
  let dye := (first == 'd' || first == 'D') &&
    (second == some '\'' || (second.map Char.toNat) == some 0x2019) &&
      (last == 'e' || last == 'E')
  4 ≤ width && width ≤ 6 && (ca || go || gi || wa || le || dye)

private def primarySplit? (config : Config) (word : String) : Option Nat :=
  if config.splitAssimilations then
    match assimilationPrefix? word with
    | some count => some count
    | none => if config.splitContractions then contractionPrefix? word else none
  else if config.splitContractions then
    contractionPrefix? word
  else
    none

private def secondarySplit? (config : Config) (word : String) : Option Nat :=
  if config.splitContractions then
    match contractionPrefix? word with
    | some count => some count
    | none => if config.splitAssimilations then assimilationPrefix? word else none
  else if config.splitAssimilations then
    assimilationPrefix? word
  else
    none

private def wordPieces (config : Config) (text : String) (start stop : text.Pos)
    (after : start < stop) : List (Token text) :=
  let unsplit := [Token.ofPositions start stop after .word]
  let maySplit :=
    (config.splitContractions && couldContract text start stop) ||
      (config.splitAssimilations && couldAssimilate text start stop)
  if maySplit then
    let original := (text.extract start stop).toLower
    match primarySplit? config original with
    | none => unsplit
    | some secondCount =>
        let firstPart := (original.take secondCount).copy
        match secondarySplit? config firstPart with
        | some firstCount =>
            (splitAtTwo? text start stop firstCount secondCount).getD unsplit
        | none =>
            match splitAt? text start stop secondCount with
            | some (left, right) => [left, right]
            | none => unsplit
  else
    unsplit

private theorem wordPieces_piecesWF (config : Config) (text : String) (start stop : text.Pos)
    (after : start < stop) : PiecesWF start stop (wordPieces config text start stop after) := by
  let maySplit :=
    (config.splitContractions && couldContract text start stop) ||
      (config.splitAssimilations && couldAssimilate text start stop)
  by_cases hMaySplit : maySplit = true
  · let original := (text.extract start stop).toLower
    cases hPrimary : primarySplit? config original with
    | none =>
        simp [wordPieces, maySplit, hMaySplit, original, hPrimary, PiecesWF,
          Tokenization.ordered, Token.ofPositions]
    | some secondCount =>
        let firstPart := (original.take secondCount).copy
        cases hSecondary : secondarySplit? config firstPart with
        | none =>
            cases hSplit : splitAt? text start stop secondCount with
            | none =>
                simp [wordPieces, maySplit, hMaySplit, original, hPrimary, firstPart, hSecondary,
                  hSplit, PiecesWF, Tokenization.ordered, Token.ofPositions]
            | some pair =>
                have splitWF := splitAt?_piecesWF text start stop secondCount
                rw [hSplit] at splitWF
                simpa [wordPieces, maySplit, hMaySplit, original, hPrimary, firstPart, hSecondary,
                  hSplit] using splitWF
        | some firstCount =>
            cases hSplit : splitAtTwo? text start stop firstCount secondCount with
            | none =>
                simp [wordPieces, maySplit, hMaySplit, original, hPrimary, firstPart, hSecondary,
                  hSplit, PiecesWF, Tokenization.ordered, Token.ofPositions]
            | some pieces =>
                have splitWF := splitAtTwo?_piecesWF text start stop firstCount secondCount
                rw [hSplit] at splitWF
                simpa [wordPieces, maySplit, hMaySplit, original, hPrimary, firstPart, hSecondary,
                  hSplit] using splitWF
  · simp [wordPieces, maySplit, hMaySplit, PiecesWF, Tokenization.ordered,
      Token.ofPositions]

private structure Scanned (text : String) where
  stop : text.Pos
  pieces : List (Token text)

private def scanWhitespaceRun (text : String) (start : text.Pos)
    (notAtEnd : start ≠ text.endPos) : Scanned text :=
  let stop := takeRest text start notAtEnd fun _ character ↦ !isWhitespace character
  ⟨stop.position, [Token.ofPositions start stop.position stop.after .word]⟩

private def scanEnglish (config : Config) (text : String) (start : text.Pos)
    (notAtEnd : start ≠ text.endPos) (first : Char) : Scanned text :=
  if isDecimalDigit first then
    let stop := takeRest text start notAtEnd (numberContinues config text)
    ⟨stop.position, [Token.ofPositions start stop.position stop.after .number]⟩
  else if isWordScalar first || (isApostrophe first && nextIsWord text start) then
    let stop := takeRest text start notAtEnd (wordContinues config text)
    ⟨stop.position, wordPieces config text start stop.position stop.after⟩
  else if isPunctuation first then
    let stop := takeRest text start notAtEnd fun _ current ↦ punctuationContinues first current
    ⟨stop.position, [Token.ofPositions start stop.position stop.after .punctuation]⟩
  else
    let stop := takeRest text start notAtEnd fun _ current ↦ symbolContinues current
    ⟨stop.position, [Token.ofPositions start stop.position stop.after .symbol]⟩

private theorem scanWhitespaceRun_piecesWF (text : String) (start : text.Pos)
    (notAtEnd : start ≠ text.endPos) :
    let scanned := scanWhitespaceRun text start notAtEnd
    PiecesWF start scanned.stop scanned.pieces := by
  simp [scanWhitespaceRun, PiecesWF, Tokenization.ordered, Token.ofPositions]

private theorem scanEnglish_piecesWF (config : Config) (text : String) (start : text.Pos)
    (notAtEnd : start ≠ text.endPos) (first : Char) :
    let scanned := scanEnglish config text start notAtEnd first
    PiecesWF start scanned.stop scanned.pieces := by
  unfold scanEnglish
  split
  · simp [PiecesWF, Tokenization.ordered, Token.ofPositions]
  · split
    · exact wordPieces_piecesWF config text start _ _
    · split <;> simp [PiecesWF, Tokenization.ordered, Token.ofPositions]

/-- Scan through ignored whitespace with an explicit iteration budget. -/
private def scanNextAux (config : Config) (text : String) : Nat → text.Pos → Option (Scanned text)
  | 0, _ => none
  | fuel + 1, position =>
      if hasCharacter : position ≠ text.endPos then
        let character := position.get hasCharacter
        if isWhitespace character then
          if config.keepNewlines && isLineBreak character then
            let stop := newlineEnd text position hasCharacter character
            some ⟨stop.position,
              [Token.ofPositions position stop.position stop.after .newline]⟩
          else
            scanNextAux config text fuel (position.next hasCharacter)
        else
          some <|
            match config.mode with
            | .whitespace => scanWhitespaceRun text position hasCharacter
            | .englishUD => scanEnglish config text position hasCharacter character
      else
        none

private theorem scanNextAux_piecesWF (config : Config) (text : String) :
    ∀ fuel position,
      match scanNextAux config text fuel position with
      | none => True
      | some scanned => PiecesWF position scanned.stop scanned.pieces := by
  intro fuel
  induction fuel with
  | zero => intro position; simp [scanNextAux]
  | succ fuel inductionHypothesis =>
      intro position
      by_cases hasCharacter : position ≠ text.endPos
      · let character := position.get hasCharacter
        by_cases whitespace : isWhitespace character = true
        · by_cases newline : (config.keepNewlines && isLineBreak character) = true
          · simp [scanNextAux, hasCharacter, character, whitespace, newline, PiecesWF,
              Tokenization.ordered, Token.ofPositions]
          · cases recursive : scanNextAux config text fuel (position.next hasCharacter) with
            | none => simp [scanNextAux, hasCharacter, character, whitespace, newline, recursive]
            | some scanned =>
                have recursiveWF := inductionHypothesis (position.next hasCharacter)
                rw [recursive] at recursiveWF
                simpa [scanNextAux, hasCharacter, character, whitespace, newline, recursive] using
                  PiecesWF.lower_mono (Std.le_of_lt String.Pos.lt_next) recursiveWF
        · cases mode : config.mode with
          | whitespace =>
              simpa [scanNextAux, hasCharacter, character, whitespace, mode] using
                scanWhitespaceRun_piecesWF text position hasCharacter
          | englishUD =>
              simpa [scanNextAux, hasCharacter, character, whitespace, mode] using
                scanEnglish_piecesWF config text position hasCharacter character
      · simp [scanNextAux, hasCharacter]

/-- Scan through ignored whitespace and produce the next nonempty source batch. -/
private def scanNext (config : Config) (text : String) (start : text.Pos) :
    Option (Scanned text) :=
  scanNextAux config text (text.utf8ByteSize + 1) start

private theorem scanNext_piecesWF (config : Config) (text : String) (start : text.Pos) :
    match scanNext config text start with
    | none => True
    | some scanned => PiecesWF start scanned.stop scanned.pieces := by
  exact scanNextAux_piecesWF config text (text.utf8ByteSize + 1) start

end Scanner

/-- A persistent streaming cursor. Pending pieces arise only from one split source word. -/
structure Cursor (text : String) where
  private mk ::
  config : Config
  position : text.Pos
  pending : List (Token text) := []

namespace Cursor

private def Valid (cursor : Cursor text) : Prop :=
  Tokenization.ordered cursor.pending = true ∧
    ∀ token ∈ cursor.pending, token.endPos ≤ cursor.position

private def ReadyAfter (boundary : text.Pos) (cursor : Cursor text) : Prop :=
  match cursor.pending with
  | [] => boundary ≤ cursor.position
  | token :: _ => boundary ≤ token.startPos

private theorem ordered_tail (token : Token text) (pending : List (Token text))
    (ordered : Tokenization.ordered (token :: pending) = true) :
    Tokenization.ordered pending = true := by
  cases pending with
  | nil => rfl
  | cons next rest =>
      change (decide (token.endPos ≤ next.startPos) &&
        Tokenization.ordered (next :: rest)) = true at ordered
      exact ((Bool.and_eq_true _ _).mp ordered).2

private theorem ordered_head_le (left right : Token text) (rest : List (Token text))
    (ordered : Tokenization.ordered (left :: right :: rest) = true) :
    left.endPos ≤ right.startPos := by
  change (decide (left.endPos ≤ right.startPos) &&
    Tokenization.ordered (right :: rest)) = true at ordered
  exact of_decide_eq_true ((Bool.and_eq_true _ _).mp ordered).1

private theorem ordered_append_singleton (tokens : List (Token text)) (token : Token text)
    (ordered : Tokenization.ordered tokens = true)
    (ready : match tokens.getLast? with
      | none => True
      | some last => last.endPos ≤ token.startPos) :
    Tokenization.ordered (tokens ++ [token]) = true := by
  induction tokens with
  | nil => simp [Tokenization.ordered]
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => simpa [Tokenization.ordered, decide_eq_true_eq] using ready
      | cons next rest =>
          have headBefore := ordered_head_le head next rest ordered
          have tailOrdered := ordered_tail head (next :: rest) ordered
          have tailReady : match (next :: rest).getLast? with
              | none => True
              | some last => last.endPos ≤ token.startPos := by
            simpa using ready
          change (decide (head.endPos ≤ next.startPos) &&
            Tokenization.ordered ((next :: rest) ++ [token])) = true
          exact (Bool.and_eq_true _ _).mpr ⟨by simpa using headBefore,
            inductionHypothesis tailOrdered tailReady⟩

/-- Begin scanning a source string. -/
@[inline] def start (config : Config) (text : String) : Cursor text :=
  ⟨config, text.startPos, []⟩

private theorem start_valid (config : Config) (text : String) : Valid (start config text) := by
  simp [Valid, start, Tokenization.ordered]

/-- Emit one token and the persistent successor cursor, or `none` at source exhaustion. -/
def next? (cursor : Cursor text) : Option (Token text × Cursor text) :=
  match cursor.pending with
  | token :: pending => some (token, { cursor with pending })
  | [] =>
      match Scanner.scanNext cursor.config text cursor.position with
      | none => none
      | some scanned =>
          match scanned.pieces with
          | [] => none
          | token :: pending =>
              some (token, ⟨cursor.config, scanned.stop, pending⟩)

private theorem next?_valid_ready (cursor : Cursor text) (valid : Valid cursor) :
    match cursor.next? with
    | none => True
    | some (token, next) => Valid next ∧ ReadyAfter token.endPos next := by
  rcases cursor with ⟨config, position, pending⟩
  cases pending with
  | nil =>
      cases scan : Scanner.scanNext config text position with
      | none => simp [next?, scan]
      | some scanned =>
          have batch := Scanner.scanNext_piecesWF config text position
          rw [scan] at batch
          simp only at batch
          cases pieces : scanned.pieces with
          | nil => simp [next?, scan, pieces]
          | cons token pending =>
              rw [pieces] at batch
              have nextValid : Valid (⟨config, scanned.stop, pending⟩ : Cursor text) := by
                refine ⟨ordered_tail token pending batch.1, ?_⟩
                intro later member
                exact (batch.2 later (by simp [member])).2
              have ready : ReadyAfter token.endPos
                  (⟨config, scanned.stop, pending⟩ : Cursor text) := by
                cases pending with
                | nil => exact (batch.2 token (by simp)).2
                | cons next rest => exact ordered_head_le token next rest batch.1
              simpa [next?, scan, pieces] using And.intro nextValid ready
  | cons token pending =>
      have nextValid : Valid (⟨config, position, pending⟩ : Cursor text) := by
        refine ⟨ordered_tail token pending valid.1, ?_⟩
        intro later member
        exact valid.2 later (by simp [member])
      have ready : ReadyAfter token.endPos
          (⟨config, position, pending⟩ : Cursor text) := by
        cases pending with
        | nil => exact valid.2 token (by simp)
        | cons next rest => exact ordered_head_le token next rest valid.1
      simpa [next?] using And.intro nextValid ready

private theorem next?_after (boundary : text.Pos) (cursor : Cursor text)
    (ready : ReadyAfter boundary cursor) :
    match cursor.next? with
    | none => True
    | some (token, _) => boundary ≤ token.startPos := by
  rcases cursor with ⟨config, position, pending⟩
  cases pending with
  | cons token pending => simpa [next?, ReadyAfter] using ready
  | nil =>
      simp only [ReadyAfter] at ready
      cases scan : Scanner.scanNext config text position with
      | none => simp [next?, scan]
      | some scanned =>
          have batch := Scanner.scanNext_piecesWF config text position
          rw [scan] at batch
          simp only at batch
          cases pieces : scanned.pieces with
          | nil => simp [next?, scan, pieces]
          | cons token pending =>
              rw [pieces] at batch
              have startsAfter : boundary ≤ token.startPos :=
                Std.le_trans ready (batch.2 token (by simp)).1
              simpa [next?, scan, pieces] using startsAfter

private def collectAux : Nat → Cursor text → Array (Token text) → Array (Token text)
  | 0, _, output => output
  | fuel + 1, current, output =>
      match current.next? with
      | none => output
      | some (token, next) => collectAux fuel next (output.push token)

private theorem collectAux_ordered (fuel : Nat) (current : Cursor text)
    (output : Array (Token text)) (valid : Valid current)
    (ordered : Tokenization.ordered output.toList = true)
    (ready : match output.toList.getLast? with
      | none => True
      | some last => ReadyAfter last.endPos current) :
    Tokenization.ordered (collectAux fuel current output).toList = true := by
  induction fuel generalizing current output with
  | zero => exact ordered
  | succ fuel inductionHypothesis =>
      rw [collectAux]
      cases step : current.next? with
      | none => exact ordered
      | some emitted =>
          rcases emitted with ⟨token, next⟩
          have nextSpec := next?_valid_ready current valid
          rw [step] at nextSpec
          simp only at nextSpec
          have startsAfter : match output.toList.getLast? with
              | none => True
              | some last => last.endPos ≤ token.startPos := by
            cases last : output.toList.getLast? with
            | none => trivial
            | some previous =>
                rw [last] at ready
                have after := next?_after previous.endPos current ready
                rw [step] at after
                exact after
          have pushedOrdered : Tokenization.ordered (output.push token).toList = true := by
            rw [Array.toList_push]
            exact ordered_append_singleton output.toList token ordered startsAfter
          have pushedReady : match (output.push token).toList.getLast? with
              | none => True
              | some last => ReadyAfter last.endPos next := by
            simpa using nextSpec.2
          exact inductionHypothesis next (output.push token) nextSpec.1 pushedOrdered pushedReady

/-- Collect every remaining token in order using at most one iteration per source byte. -/
def collect (cursor : Cursor text) : Array (Token text) :=
  collectAux (text.utf8ByteSize + 1) cursor
    (Array.emptyWithCapacity (text.utf8ByteSize / 4 + 1))

private theorem collect_ordered_of_valid (cursor : Cursor text) (valid : Valid cursor) :
    Tokenization.ordered cursor.collect.toList = true := by
  apply collectAux_ordered (text.utf8ByteSize + 1) cursor
    (Array.emptyWithCapacity (text.utf8ByteSize / 4 + 1)) valid
  · simp [Tokenization.ordered]
  · simp

/-- Collection preserves source order when a cursor's pending split pieces are valid. -/
theorem collect_ordered (cursor : Cursor text)
    (pendingOrdered : Tokenization.ordered cursor.pending = true)
    (pendingEndsBeforePosition : ∀ token ∈ cursor.pending, token.endPos ≤ cursor.position) :
    Tokenization.ordered cursor.collect.toList = true :=
  collect_ordered_of_valid cursor ⟨pendingOrdered, pendingEndsBeforePosition⟩

end Cursor

/-- A reusable rule tokenizer. Its total configuration needs no effectful compilation step. -/
structure Tokenizer where
  config : Config := {}
  deriving Repr, DecidableEq, Inhabited

namespace Tokenizer

/-- The production English/UD-core tokenizer. -/
def default : Tokenizer := {}

/-- Open a streaming cursor over one source string. -/
@[inline] def cursor (tokenizer : Tokenizer) (text : String) : Cursor text :=
  Cursor.start tokenizer.config text

/-- Tokenize a complete string into source-indexed tokens. -/
def tokenize (tokenizer : Tokenizer) (text : String) : Tokenization :=
  ⟨text, (tokenizer.cursor text).collect⟩

/-- Complete tokenization emits nonoverlapping tokens in source order. -/
theorem tokenize_wf (tokenizer : Tokenizer) (text : String) :
    (tokenizer.tokenize text).WF := by
  change Tokenization.ordered (tokenizer.cursor text).collect.toList = true
  apply Cursor.collect_ordered_of_valid
  simpa [cursor] using Cursor.start_valid tokenizer.config text

end Tokenizer

/-- Convenience entry point for one-off tokenization with explicit or default options. -/
@[inline] def tokenize (text : String) (config : Config := {}) : Tokenization :=
  (Tokenizer.mk config).tokenize text

end Nlp.Tokenize
