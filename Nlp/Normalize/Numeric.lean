import Init.Data.Rat
import Nlp.Core.Doc

/-!
# Exact bounded English numeric normalization

This module recognizes exact ASCII numeric literals and English cardinal or ordinal expressions.
Values use Lean's reduced arbitrary-precision `Rat`; no binary floating-point approximation enters
the public result. Percentages, currencies, units, and temporal interpretation deliberately remain
separate semantic layers.
-/

namespace Nlp.Normalize.Numeric

/-- Resource limits checked by the literal and document normalizers. -/
structure Config where
  /-- Maximum tokens retained by one normalized mention. -/
  maxTokensPerMention : Nat := 32
  /-- Maximum aggregate UTF-8 bytes in the token forms of one mention. -/
  maxBytesPerMention : Nat := 512
  /-- Maximum ASCII digits read from one literal, including an exponent. -/
  maxDigits : Nat := 128
  /-- Maximum absolute decimal exponent accepted from scientific notation. -/
  maxExponent : Nat := 128
  /-- Maximum decimal digits in a pre-reduction exact numerator or denominator. -/
  maxValueDigits : Nat := 256
  /-- Maximum successful prefix candidates considered by one extraction. -/
  maxCandidates : Nat := 65_536
  /-- Maximum mentions retained by one extraction. -/
  maxMentions : Nat := 65_536
  /-- Maximum conservative token/byte work charged before extraction. -/
  maxWork : Nat := 16_777_216
  deriving Repr, DecidableEq, Inhabited

/-- The two interpretation classes in this first normalization tranche. -/
inductive Kind where
  | cardinal
  | ordinal
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- An exact reduced rational value. -/
structure Value where
  private mk ::
  /-- Canonical numerator and positive coprime denominator. -/
  rational : Rat
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace Value

/-- Embed an already reduced Lean rational. -/
@[inline] def ofRat (value : Rat) : Value :=
  .mk value

/-- Embed an integer exactly. -/
@[inline] def ofInt (value : Int) : Value :=
  .mk value

/-- Embed a natural number exactly. -/
@[inline] def ofNat (value : Nat) : Value :=
  .mk value

/-- Exact rational addition. -/
@[inline] def add (left right : Value) : Value :=
  .mk (left.rational + right.rational)

/-- Exact rational multiplication. -/
@[inline] def mul (left right : Value) : Value :=
  .mk (left.rational * right.rational)

instance : ToString Value := ⟨fun value ↦ toString value.rational⟩

end Value

/-- One exact value sealed against its source and selected-range columns. -/
structure Mention (source : Array String) (ranges : Array (Nat × Nat)) where
  private mk ::
  /-- Ordinal of the selected range that produced this mention. -/
  rangeOrdinal : Nat
  /-- The selected range ordinal is present in the sealed range column. -/
  private rangeExists : rangeOrdinal < ranges.size
  /-- Inclusive token offset in the original full token column. -/
  start : Nat
  /-- Exclusive token offset in the original full token column. -/
  stop : Nat
  /-- Cardinal or ordinal interpretation. -/
  kind : Kind
  /-- Exact reduced value. -/
  value : Value
  /-- Every public mention contains at least one source token. -/
  private nonempty : start < stop
  /-- A mention never begins before its selected range. -/
  private startsInRange : (ranges[rangeOrdinal]'rangeExists).1 ≤ start
  /-- A mention never ends after its selected range. -/
  private stopsInRange : stop ≤ (ranges[rangeOrdinal]'rangeExists).2
  /-- The selected range is itself bounded by the full source column. -/
  private rangeInSource : (ranges[rangeOrdinal]'rangeExists).2 ≤ source.size
  deriving Repr, DecidableEq

namespace Mention

/-- Complete source token count carried by a sealed mention's type. -/
@[inline] def sourceSize (_mention : Mention source ranges) : Nat :=
  source.size

/-- Selected range carried by a sealed mention's range ordinal. -/
@[inline] def selectedRange (mention : Mention source ranges) : Nat × Nat :=
  ranges[mention.rangeOrdinal]'mention.rangeExists

/-- Inclusive lower bound of the selected range. -/
@[inline] def rangeStart (mention : Mention source ranges) : Nat :=
  mention.selectedRange.1

/-- Exclusive upper bound of the selected range. -/
@[inline] def rangeStop (mention : Mention source ranges) : Nat :=
  mention.selectedRange.2

/-- Every normalized mention has a positive token width. -/
theorem start_lt_stop (mention : Mention source ranges) : mention.start < mention.stop :=
  mention.nonempty

/-- Every normalized mention starts within its selected range. -/
theorem rangeStart_le_start (mention : Mention source ranges) :
    mention.rangeStart ≤ mention.start :=
  mention.startsInRange

/-- Every normalized mention stops within its selected range. -/
theorem stop_le_rangeStop (mention : Mention source ranges) :
    mention.stop ≤ mention.rangeStop :=
  mention.stopsInRange

/-- Every normalized mention is bounded by its complete source token column. -/
theorem stop_le_sourceSize (mention : Mention source ranges) :
    mention.stop ≤ mention.sourceSize := by
  exact Nat.le_trans mention.stopsInRange mention.rangeInSource

/-- A normalized mention's selected range occurs in its sealed range column. -/
theorem selectedRange_mem (mention : Mention source ranges) :
    mention.selectedRange ∈ ranges :=
  Array.getElem_mem mention.rangeExists

/-- Number of source tokens covered by a mention. -/
@[inline] def width (mention : Mention source ranges) : Nat :=
  mention.stop - mention.start

end Mention

/--
A sealed normalization result retaining the source forms, selected ranges, and checked mentions.

The only constructor is internal, so every mention was produced from this source and one of these
ranges after validation.
-/
structure Result where
  private mk ::
  /-- Complete token forms whose coordinates appear in the result. -/
  source : Array String
  /-- Caller-selected half-open ranges, retained in caller order. -/
  ranges : Array (Nat × Nat)
  /-- Deterministic longest-leftmost normalized mentions. -/
  mentions : Array (Mention source ranges)
  deriving Repr, DecidableEq

namespace Result

/-- Number of normalized mentions retained by a result. -/
@[inline] def size (result : Result) : Nat :=
  result.mentions.size

/-- A retained mention's source-size witness agrees with its enclosing result. -/
theorem mention_sourceAligned (result : Result)
    (mention : Mention result.source result.ranges)
    (_member : mention ∈ result.mentions) : mention.sourceSize = result.source.size :=
  rfl

/-- A retained mention's checked range belongs to its enclosing result. -/
theorem mention_rangeSelected (result : Result)
    (mention : Mention result.source result.ranges)
    (_member : mention ∈ result.mentions) :
    (mention.rangeStart, mention.rangeStop) ∈ result.ranges :=
  mention.selectedRange_mem

/-- A retained mention's exclusive stop is bounded by its enclosing result's source. -/
theorem mention_stop_le_source (result : Result)
    (mention : Mention result.source result.ranges)
    (_member : mention ∈ result.mentions) : mention.stop ≤ result.source.size :=
  mention.stop_le_sourceSize

end Result

/-- Why a strict ASCII numeric literal was rejected. -/
inductive LiteralError where
  | empty
  | byteBudget (required limit : Nat)
  | digitBudget (required limit : Nat)
  | exponentBudget (required limit : Nat)
  | valueDigitBudget (required limit : Nat)
  | invalidSyntax
  | invalidGrouping
  | invalidOrdinalSuffix (suffix : String) (value : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A directly parsed literal together with its interpretation class. -/
structure Parsed where
  kind : Kind
  value : Value
  deriving Repr, DecidableEq, Inhabited

private inductive Split where
  | absent (all : List Char)
  | once (left right : List Char)
  | multiple

private structure SplitScan where
  found : Bool := false
  multiple : Bool := false
  leftRev : List Char := []
  rightRev : List Char := []

/-- Split a character list iteratively, rejecting a second delimiter without recursive descent. -/
private def splitOnce (delimiter : Char → Bool) (characters : List Char) : Split :=
  let scan := characters.foldl (init := ({} : SplitScan)) fun scan character ↦
    if scan.multiple then
      scan
    else if delimiter character then
      if scan.found then { scan with multiple := true }
      else { scan with found := true }
    else if scan.found then
      { scan with rightRev := character :: scan.rightRev }
    else
      { scan with leftRev := character :: scan.leftRev }
  if scan.multiple then
    .multiple
  else if scan.found then
    .once scan.leftRev.reverse scan.rightRev.reverse
  else
    .absent scan.leftRev.reverse

@[inline] private def asciiDigit? (character : Char) : Option Nat :=
  if '0' ≤ character && character ≤ '9' then
    some (character.toNat - '0'.toNat)
  else
    none

private structure Digits where
  value : Nat
  count : Nat

private def parsePlainDigitsGo (config : Config) (prior : Nat) : List Char → Nat → Nat →
    Except LiteralError Digits
  | [], value, count =>
      if count = 0 then .error .invalidSyntax else .ok ⟨value, count⟩
  | character :: rest, value, count => do
      let digit ←
        match asciiDigit? character with
        | some digit => pure digit
        | none => throw .invalidSyntax
      let required := prior + count + 1
      if config.maxDigits < required then
        throw <| .digitBudget required config.maxDigits
      parsePlainDigitsGo config prior rest (value * 10 + digit) (count + 1)

@[inline] private def parsePlainDigits (config : Config) (characters : List Char) :
    Except LiteralError Digits :=
  parsePlainDigitsGo config 0 characters 0 0

@[inline] private def parsePlainDigitsAfter (config : Config) (prior : Nat)
    (characters : List Char) : Except LiteralError Digits :=
  parsePlainDigitsGo config prior characters 0 0

private structure IntegerDigits where
  value : Nat
  count : Nat
  grouped : Bool

private def validFinishedGroup (groups groupWidth : Nat) : Bool :=
  if groups = 0 then 0 < groupWidth else groupWidth = 3

private def parseIntegerGo (config : Config) : List Char → Nat → Nat → Nat → Nat →
    Except LiteralError IntegerDigits
  | [], value, digits, groups, groupWidth =>
      if validFinishedGroup groups groupWidth then
        .ok ⟨value, digits, groups != 0⟩
      else
        .error .invalidGrouping
  | character :: rest, value, digits, groups, groupWidth =>
      if character == ',' then
        let valid := if groups = 0 then 0 < groupWidth && groupWidth ≤ 3 else groupWidth = 3
        if valid then
          parseIntegerGo config rest value digits (groups + 1) 0
        else
          .error .invalidGrouping
      else do
        let digit ←
          match asciiDigit? character with
          | some digit => pure digit
          | none => throw .invalidSyntax
        let required := digits + 1
        if config.maxDigits < required then
          throw <| .digitBudget required config.maxDigits
        parseIntegerGo config rest (value * 10 + digit) required groups (groupWidth + 1)

@[inline] private def parseInteger (config : Config) (characters : List Char) :
    Except LiteralError IntegerDigits :=
  parseIntegerGo config characters 0 0 0 0

private def lowerAscii (character : Char) : Char :=
  if 'A' ≤ character && character ≤ 'Z' then
    Char.ofNat (character.toNat + ('a'.toNat - 'A'.toNat))
  else
    character

private structure OrdinalCore where
  core : List Char
  suffix : Option String

private def stripOrdinalSuffix (characters : List Char) : OrdinalCore :=
  match characters.reverse with
  | second :: first :: rest =>
      let suffix := String.ofList [lowerAscii first, lowerAscii second]
      if suffix == "st" || suffix == "nd" || suffix == "rd" || suffix == "th" then
        ⟨rest.reverse, some suffix⟩
      else
        ⟨characters, none⟩
  | _ => ⟨characters, none⟩

private def validOrdinalSuffix (value : Nat) (suffix : String) : Bool :=
  let lastTwo := value % 100
  let expected :=
    if lastTwo = 11 || lastTwo = 12 || lastTwo = 13 then
      "th"
    else
      match value % 10 with
      | 1 => "st"
      | 2 => "nd"
      | 3 => "rd"
      | _ => "th"
  suffix == expected

private structure Exponent where
  negative : Bool
  magnitude : Nat
  digits : Nat

private def parseExponent (config : Config) (prior : Nat) (characters : List Char) :
    Except LiteralError Exponent := do
  let (negative, body) :=
    match characters with
    | '+' :: rest => (false, rest)
    | '-' :: rest => (true, rest)
    | _ => (false, characters)
  let parsed ← parsePlainDigitsAfter config prior body
  if config.maxExponent < parsed.value then
    throw <| .exponentBudget parsed.value config.maxExponent
  return ⟨negative, parsed.value, parsed.count⟩

private structure Mantissa where
  coefficient : Nat
  fractionalDigits : Nat
  digits : Nat
  hasFraction : Bool

private def parseMantissa (config : Config) (characters : List Char) :
    Except LiteralError Mantissa := do
  match splitOnce (· == '.') characters with
  | .multiple => throw .invalidSyntax
  | .absent integerChars =>
      let integer ← parseInteger config integerChars
      return ⟨integer.value, 0, integer.count, false⟩
  | .once integerChars fractionChars =>
      let integer ← parseInteger config integerChars
      let fraction ← parsePlainDigitsAfter config integer.count fractionChars
      let totalDigits := integer.count + fraction.count
      if config.maxDigits < totalDigits then
        throw <| .digitBudget totalDigits config.maxDigits
      let coefficient := integer.value * 10 ^ fraction.count + fraction.value
      return ⟨coefficient, fraction.count, totalDigits, true⟩

private def exactValue (config : Config) (negative : Bool) (mantissa : Mantissa)
    (exponent : Exponent) : Except LiteralError Value := do
  let (numeratorPower, denominatorPower) :=
    if exponent.negative then
      (0, mantissa.fractionalDigits + exponent.magnitude)
    else if mantissa.fractionalDigits ≤ exponent.magnitude then
      (exponent.magnitude - mantissa.fractionalDigits, 0)
    else
      (0, mantissa.fractionalDigits - exponent.magnitude)
  let coefficientDigits := (Nat.toDigits 10 mantissa.coefficient).length
  let numeratorDigits :=
    if mantissa.coefficient = 0 then 1 else coefficientDigits + numeratorPower
  let denominatorDigits := denominatorPower + 1
  let requiredDigits := max numeratorDigits denominatorDigits
  if config.maxValueDigits < requiredDigits then
    throw <| .valueDigitBudget requiredDigits config.maxValueDigits
  if mantissa.coefficient = 0 then
    return .ofRat 0
  let unsigned := mantissa.coefficient * 10 ^ numeratorPower
  let numerator : Int := if negative then -(Int.ofNat unsigned) else Int.ofNat unsigned
  let denominator := 10 ^ denominatorPower
  have denominatorPositive : 0 < denominator := Nat.pow_pos (by decide)
  return .ofRat (Rat.normalize numerator denominator (Nat.ne_of_gt denominatorPositive))

/--
Parse one strict ASCII signed, grouped, decimal, or scientific literal exactly.

Digit ordinals are accepted only for integral unsigned forms with the arithmetically correct
`st`, `nd`, `rd`, or `th` suffix. Grouping commas must separate a one-to-three-digit first group
from exact three-digit later groups.
-/
def parseLiteralWith (config : Config) (source : String) : Except LiteralError Parsed := do
  let bytes := source.utf8ByteSize
  if config.maxBytesPerMention < bytes then
    throw <| .byteBudget bytes config.maxBytesPerMention
  if source.isEmpty then
    throw .empty
  let ordinal := stripOrdinalSuffix source.toList
  let (negative, unsigned) :=
    match ordinal.core with
    | '+' :: rest => (false, rest)
    | '-' :: rest => (true, rest)
    | _ => (false, ordinal.core)
  match ordinal.suffix with
  | some suffix =>
      if negative || unsigned != ordinal.core then
        throw .invalidSyntax
      let integer ← parseInteger config unsigned
      if validOrdinalSuffix integer.value suffix then
        let requiredDigits := (Nat.toDigits 10 integer.value).length
        if config.maxValueDigits < requiredDigits then
          throw <| .valueDigitBudget requiredDigits config.maxValueDigits
        return ⟨.ordinal, .ofNat integer.value⟩
      throw <| .invalidOrdinalSuffix suffix integer.value
  | none =>
      let (mantissa, exponent) ←
        match splitOnce (fun character ↦ character == 'e' || character == 'E') unsigned with
        | .multiple => throw .invalidSyntax
        | .absent mantissaChars =>
            pure (← parseMantissa config mantissaChars, ⟨false, 0, 0⟩)
        | .once mantissaChars exponentChars => do
            let mantissa ← parseMantissa config mantissaChars
            pure (mantissa, ← parseExponent config mantissa.digits exponentChars)
      let totalDigits := mantissa.digits + exponent.digits
      if config.maxDigits < totalDigits then
        throw <| .digitBudget totalDigits config.maxDigits
      return ⟨.cardinal, ← exactValue config negative mantissa exponent⟩

/-- Parse one literal with the production resource policy. -/
@[inline] def parseLiteral (source : String) : Except LiteralError Parsed :=
  parseLiteralWith {} source

/-- Why range or document extraction could not complete under its checked policy. -/
inductive Error where
  | invalidRange (ordinal start stop size : Nat)
  | input (cause : Doc.SemanticError)
  | literal (token : Nat) (source : String) (cause : LiteralError)
  | tokenBudget (start required limit : Nat)
  | byteBudget (start required limit : Nat)
  | candidateBudget (required limit : Nat)
  | mentionBudget (required limit : Nat)
  | workBudget (required limit : Nat)
  | valueDigitBudget (start required limit : Nat)
  | notSingleExpression (start stop : Nat)
  | outputInvariant
  deriving Repr, DecidableEq

private inductive Atom where
  | small (value : Nat)
  | tens (value : Nat)
  | hundred
  | scale (value : Nat)
  | ordinalSmall (value : Nat)
  | ordinalTens (value : Nat)
  | ordinalHundred
  | ordinalScale (value : Nat)
  | conjunction
  | comma
  | hyphen
  | positive
  | negative
  | indefinite
  | literal (parsed : Parsed)
  | other
  deriving Repr, DecidableEq, Inhabited

private structure Lexeme where
  atom : Atom
  bytes : Nat
  deriving Inhabited

private def wordAtom : String → Atom
  | "zero" => .small 0
  | "one" => .small 1
  | "two" => .small 2
  | "three" => .small 3
  | "four" => .small 4
  | "five" => .small 5
  | "six" => .small 6
  | "seven" => .small 7
  | "eight" => .small 8
  | "nine" => .small 9
  | "ten" => .small 10
  | "eleven" => .small 11
  | "twelve" => .small 12
  | "thirteen" => .small 13
  | "fourteen" => .small 14
  | "fifteen" => .small 15
  | "sixteen" => .small 16
  | "seventeen" => .small 17
  | "eighteen" => .small 18
  | "nineteen" => .small 19
  | "twenty" => .tens 20
  | "thirty" => .tens 30
  | "forty" => .tens 40
  | "fifty" => .tens 50
  | "sixty" => .tens 60
  | "seventy" => .tens 70
  | "eighty" => .tens 80
  | "ninety" => .tens 90
  | "hundred" => .hundred
  | "thousand" => .scale 1_000
  | "million" => .scale 1_000_000
  | "billion" => .scale 1_000_000_000
  | "trillion" => .scale 1_000_000_000_000
  | "zeroth" => .ordinalSmall 0
  | "first" => .ordinalSmall 1
  | "second" => .ordinalSmall 2
  | "third" => .ordinalSmall 3
  | "fourth" => .ordinalSmall 4
  | "fifth" => .ordinalSmall 5
  | "sixth" => .ordinalSmall 6
  | "seventh" => .ordinalSmall 7
  | "eighth" => .ordinalSmall 8
  | "ninth" => .ordinalSmall 9
  | "tenth" => .ordinalSmall 10
  | "eleventh" => .ordinalSmall 11
  | "twelfth" => .ordinalSmall 12
  | "thirteenth" => .ordinalSmall 13
  | "fourteenth" => .ordinalSmall 14
  | "fifteenth" => .ordinalSmall 15
  | "sixteenth" => .ordinalSmall 16
  | "seventeenth" => .ordinalSmall 17
  | "eighteenth" => .ordinalSmall 18
  | "nineteenth" => .ordinalSmall 19
  | "twentieth" => .ordinalTens 20
  | "thirtieth" => .ordinalTens 30
  | "fortieth" => .ordinalTens 40
  | "fiftieth" => .ordinalTens 50
  | "sixtieth" => .ordinalTens 60
  | "seventieth" => .ordinalTens 70
  | "eightieth" => .ordinalTens 80
  | "ninetieth" => .ordinalTens 90
  | "hundredth" => .ordinalHundred
  | "thousandth" => .ordinalScale 1_000
  | "millionth" => .ordinalScale 1_000_000
  | "billionth" => .ordinalScale 1_000_000_000
  | "trillionth" => .ordinalScale 1_000_000_000_000
  | "and" => .conjunction
  | "plus" | "positive" => .positive
  | "minus" | "negative" => .negative
  | "a" | "an" => .indefinite
  | _ => .other

private def literalCharacter (character : Char) : Bool :=
  ('0' ≤ character && character ≤ '9') || character == '+' || character == '-' ||
    character == ',' || character == '.' || character == 'e' || character == 'E'

private def literalCoreCharacter (character : Char) : Bool :=
  ('0' ≤ character && character ≤ '9') || character == '+' || character == '-' ||
    character == ',' || character == '.' || character == 'e' || character == 'E'

private def looksLikeLiteral (source : String) : Bool :=
  let characters := source.toList
  match characters with
  | [] => false
  | first :: _ =>
      (('0' ≤ first && first ≤ '9') || first == '+' || first == '-') &&
        let ordinal := stripOrdinalSuffix characters
        match ordinal.suffix with
        | some _ => !ordinal.core.isEmpty && ordinal.core.all fun character ↦
            ('0' ≤ character && character ≤ '9') || character == ',' ||
              character == '+' || character == '-'
        | none => source.all literalCharacter

private structure OversizeLiteralScan where
  suffixLetters : Nat := 0
  prior : Char := Char.ofNat 0
  last : Char := Char.ofNat 0
  allCore : Bool := true
  allOrdinal : Bool := true

private def ordinalSuffixCharacter (character : Char) : Bool :=
  let lowered := lowerAscii character
  lowered == 's' || lowered == 't' || lowered == 'n' || lowered == 'd' ||
    lowered == 'r' || lowered == 'h'

private def oversizeLiteralStep (scan : OversizeLiteralScan)
    (character : Char) : OversizeLiteralScan :=
  let suffix := ordinalSuffixCharacter character
  { suffixLetters := scan.suffixLetters + if suffix then 1 else 0
    prior := scan.last
    last := lowerAscii character
    allCore := scan.allCore && literalCoreCharacter character
    allOrdinal := scan.allOrdinal && (literalCoreCharacter character || suffix) }

private def validSuffixPair (left right : Char) : Bool :=
  (left == 's' && right == 't') || (left == 'n' && right == 'd') ||
    (left == 'r' && right == 'd') || (left == 't' && right == 'h')

private def looksLikeOversizeLiteral (source : String) : Bool :=
  match source.front? with
  | none => false
  | some first =>
      let scan := source.foldl oversizeLiteralStep {}
      (('0' ≤ first && first ≤ '9') || first == '+' || first == '-') &&
        (scan.allCore || (scan.allOrdinal && scan.suffixLetters == 2 &&
          validSuffixPair scan.prior scan.last))

private def classify (config : Config) (token : Nat) (source : String) : Except Error Lexeme := do
  let bytes := source.utf8ByteSize
  let atom ←
    if source == "," then
      pure .comma
    else if source == "-" then
      pure .hyphen
    else if source == "+" then
      pure .positive
    else
      let word := if bytes ≤ 16 then wordAtom source.toLower else .other
      if word != .other && config.maxBytesPerMention < bytes then
        throw <| .byteBudget token bytes config.maxBytesPerMention
      else if word != .other then
        pure word
      else if config.maxBytesPerMention < bytes then
        if looksLikeOversizeLiteral source then
          throw <| .literal token source (.byteBudget bytes config.maxBytesPerMention)
        else
          pure .other
      else if looksLikeLiteral source then
        match parseLiteralWith config source with
        | .ok parsed => pure (.literal parsed)
        | .error cause => throw <| .literal token source cause
      else
        pure .other
  return ⟨atom, bytes⟩

private inductive GroupState where
  | start
  | implicitOne
  | small
  | tens
  | literal
  | hundred
  | hundredTens
  | hundredSmall
  deriving Repr, DecidableEq

private inductive Pending where
  | none
  | hyphen
  | join
  | comma
  deriving Repr, DecidableEq

private structure Scan where
  total : Rat := 0
  group : Rat := 0
  state : GroupState := .start
  pending : Pending := .none
  lastScale : Nat := 1_000_000_000_000_000
  negative : Bool := false
  signSeen : Bool := false
  semantic : Bool := false

private inductive Step where
  | stop
  | valueBudget (required : Nat)
  | next (scan : Scan) (accepted : Option Parsed := none) (terminal : Bool := false)

@[inline] private def signed (scan : Scan) (value : Rat) : Rat :=
  if scan.negative then -value else value

@[inline] private def decimalDigits (value : Nat) : Nat :=
  (Nat.toDigits 10 value).length

@[inline] private def signedDecimalDigits (value : Int) : Nat :=
  decimalDigits value.natAbs

private structure RawRat where
  numerator : Int
  denominator : Nat
  positive : 0 < denominator

namespace RawRat

@[inline] private def valueDigits (raw : RawRat) : Nat :=
  max (signedDecimalDigits raw.numerator) (decimalDigits raw.denominator)

@[inline] private def normalize (raw : RawRat) : Rat :=
  Rat.normalize raw.numerator raw.denominator (Nat.ne_of_gt raw.positive)

end RawRat

/-- Construct the exact unreduced common-denominator addition without allocating a `Rat`. -/
private def rawAdd (left right : Rat) : RawRat :=
  { numerator := left.num * Int.ofNat right.den + right.num * Int.ofNat left.den
    denominator := left.den * right.den
    positive := Nat.mul_pos left.den_pos right.den_pos }

/-- Construct the exact unreduced product without allocating a `Rat`. -/
private def rawMul (left right : Rat) : RawRat :=
  { numerator := left.num * right.num
    denominator := left.den * right.den
    positive := Nat.mul_pos left.den_pos right.den_pos }

/-- Check exact pre-reduction width before allocating a rational addition result. -/
private def addRatWith (config : Config) (left right : Rat) : Except Nat Rat :=
  let raw := rawAdd left right
  let required := raw.valueDigits
  if config.maxValueDigits < required then .error required else .ok raw.normalize

/-- Check exact pre-reduction width before allocating a rational multiplication result. -/
private def mulRatWith (config : Config) (left right : Rat) : Except Nat Rat :=
  let raw := rawMul left right
  let required := raw.valueDigits
  if config.maxValueDigits < required then .error required else .ok raw.normalize

@[inline] private def accepted (scan : Scan) (kind : Kind) (raw : Rat) : Parsed :=
  ⟨kind, .ofRat (signed scan raw)⟩

private def acceptTotal (config : Config) (scan : Scan) (kind : Kind)
    (terminal : Bool := false) : Step :=
  match addRatWith config scan.total scan.group with
  | .error required => .valueBudget required
  | .ok raw => .next scan (some (accepted scan kind raw)) terminal

private def smallPositive? (value : Rat) : Option Nat :=
  if value.den = 1 && 0 < value.num then
    let natural := value.num.toNat
    if natural ≤ 99 then some natural else none
  else
    none

private def smallNonnegative? (value : Rat) : Option Nat :=
  if value.den = 1 && 0 ≤ value.num then
    let natural := value.num.toNat
    if natural ≤ 99 then some natural else none
  else
    none

private def pendingAllows (pending : Pending) (atom : Atom) : Bool :=
  match pending, atom with
  | .none, _ => true
  | .hyphen, .small value | .hyphen, .ordinalSmall value => 1 ≤ value && value ≤ 9
  | .join, .small _ | .join, .tens _ | .join, .ordinalSmall _
  | .join, .ordinalTens _ | .join, .literal _ | .join, .indefinite => true
  | .comma, .small _ | .comma, .tens _ | .comma, .ordinalSmall _
  | .comma, .ordinalTens _ | .comma, .literal _ | .comma, .indefinite => true
  | _, _ => false

private def stepSmall (config : Config) (scan : Scan) (value : Nat)
    (ordinal : Bool) : Step :=
  if ordinal && scan.signSeen then
    .stop
  else if !pendingAllows scan.pending
      (if ordinal then .ordinalSmall value else .small value) then
    .stop
  else
    let scan := { scan with pending := .none, semantic := true }
    let finish (next : Scan) :=
      let kind := if ordinal then Kind.ordinal else Kind.cardinal
      acceptTotal config next kind ordinal
    match scan.state with
    | .start => finish { scan with group := value, state := .small }
    | .tens =>
        if 1 ≤ value && value ≤ 9 then
          match addRatWith config scan.group value with
          | .error required => .valueBudget required
          | .ok group => finish { scan with group, state := .small }
        else
          .stop
    | .hundred =>
        match addRatWith config scan.group value with
        | .error required => .valueBudget required
        | .ok group => finish { scan with group, state := .hundredSmall }
    | .hundredTens =>
        if 1 ≤ value && value ≤ 9 then
          match addRatWith config scan.group value with
          | .error required => .valueBudget required
          | .ok group => finish { scan with group, state := .hundredSmall }
        else
          .stop
    | _ => .stop

private def stepTens (config : Config) (scan : Scan) (value : Nat)
    (ordinal : Bool) : Step :=
  if ordinal && scan.signSeen then
    .stop
  else if !pendingAllows scan.pending
      (if ordinal then .ordinalTens value else .tens value) then
    .stop
  else
    let scan := { scan with pending := .none, semantic := true }
    let finish (next : Scan) :=
      let kind := if ordinal then Kind.ordinal else Kind.cardinal
      acceptTotal config next kind ordinal
    match scan.state with
    | .start => finish { scan with group := value, state := .tens }
    | .hundred =>
        match addRatWith config scan.group value with
        | .error required => .valueBudget required
        | .ok group => finish { scan with group, state := .hundredTens }
    | _ => .stop

private def stepLiteral (config : Config) (scan : Scan) (parsed : Parsed) : Step :=
  if !pendingAllows scan.pending (.literal parsed) then
    .stop
  else
    let raw := parsed.value.rational
    match parsed.kind, scan.state with
    | .cardinal, .start =>
        if scan.signSeen && raw.num < 0 then
          .stop
        else
          let next :=
            { scan with
              group := raw
              state := .literal
              pending := .none
              semantic := true }
          acceptTotal config next .cardinal
    | .ordinal, .start =>
        if scan.signSeen then
          .stop
        else
          let next :=
            { scan with
              group := raw
              state := .small
              pending := .none
              semantic := true }
          acceptTotal config next .ordinal true
    | .ordinal, .tens | .ordinal, .hundredTens =>
        match smallPositive? raw with
        | some value => stepSmall config scan value true
        | none => .stop
    | .ordinal, .hundred =>
        match smallNonnegative? raw with
        | some value => stepSmall config scan value true
        | none => .stop
    | _, _ => .stop

private def stepHundred (config : Config) (scan : Scan) (ordinal : Bool) : Step :=
  if ordinal && scan.signSeen then
    .stop
  else if scan.pending != .none then
    .stop
  else
    match scan.state, smallPositive? scan.group with
    | .small, some _ | .literal, some _ | .implicitOne, some _ =>
        match mulRatWith config scan.group 100 with
        | .error required => .valueBudget required
        | .ok group =>
            let next := { scan with group, state := .hundred, semantic := true }
            let kind := if ordinal then Kind.ordinal else Kind.cardinal
            acceptTotal config next kind ordinal
    | _, _ => .stop

private def stepScale (config : Config) (scan : Scan) (scale : Nat)
    (ordinal : Bool) : Step :=
  if ordinal && scan.signSeen then
    .stop
  else if scan.pending != .none || scan.state == .start || scan.lastScale ≤ scale ||
      scan.group == 0 then
    .stop
  else
    match mulRatWith config scan.group scale with
    | .error required => .valueBudget required
    | .ok scaled =>
        match addRatWith config scan.total scaled with
        | .error required => .valueBudget required
        | .ok raw =>
            let next :=
              { scan with
                total := raw
                group := 0
                state := .start
                lastScale := scale
                semantic := true }
            let kind := if ordinal then Kind.ordinal else Kind.cardinal
            .next next (some (accepted next kind raw)) ordinal

private def stepAtom (config : Config) (scan : Scan) (atom : Atom) : Step :=
  match atom with
  | .other => .stop
  | .small value => stepSmall config scan value false
  | .tens value => stepTens config scan value false
  | .ordinalSmall value => stepSmall config scan value true
  | .ordinalTens value => stepTens config scan value true
  | .literal parsed => stepLiteral config scan parsed
  | .hundred => stepHundred config scan false
  | .ordinalHundred => stepHundred config scan true
  | .scale value => stepScale config scan value false
  | .ordinalScale value => stepScale config scan value true
  | .indefinite =>
      if pendingAllows scan.pending .indefinite && scan.state == .start then
        .next { scan with group := 1, state := .implicitOne, pending := .none }
      else
        .stop
  | .positive | .negative =>
      if !scan.signSeen && !scan.semantic && scan.state == .start && scan.pending == .none then
        .next { scan with negative := atom == .negative, signSeen := true }
      else
        .stop
  | .hyphen =>
      if !scan.signSeen && !scan.semantic && scan.state == .start && scan.pending == .none then
        .next { scan with negative := true, signSeen := true }
      else if scan.pending == .none &&
          (scan.state == .tens || scan.state == .hundredTens) then
        .next { scan with pending := .hyphen }
      else
        .stop
  | .conjunction =>
      if scan.pending == .comma then
        .next { scan with pending := .join }
      else if scan.pending == .none &&
          (scan.state == .hundred || (scan.state == .start && scan.semantic)) then
        .next { scan with pending := .join }
      else
        .stop
  | .comma =>
      if scan.pending == .none &&
          (scan.state == .hundred || (scan.state == .start && scan.semantic)) then
        .next { scan with pending := .comma }
      else
        .stop

private def startsMention : Atom → Bool
  | .small _ | .tens _ | .literal _ | .ordinalSmall _ | .ordinalTens _ => true
  | .indefinite | .positive | .negative | .hyphen => true
  | _ => false

private structure Found where
  width : Nat
  positive : 0 < width
  parsed : Parsed
  candidates : Nat

private def longestAt (config : Config) (lexemes : Array Lexeme) (base offset : Nat)
    (candidateBase : Nat) : Except Error (Option Found) := do
  if config.maxTokensPerMention = 0 && offset < lexemes.size &&
      startsMention lexemes[offset]!.atom then
    throw <| .tokenBudget (base + offset) 1 0
  let mut scan : Scan := {}
  let mut bytes := 0
  let mut last : Option Found := none
  let mut candidates := 0
  let available := min config.maxTokensPerMention (lexemes.size - offset)
  for width in [0:available] do
    let lexeme := lexemes[offset + width]!
    if lexeme.atom == .other then
      return last
    match stepAtom config scan lexeme.atom with
    | .stop => return last
    | .valueBudget required =>
        throw <| .valueDigitBudget (base + offset) required config.maxValueDigits
    | .next next acceptedValue terminal =>
        let requiredBytes := bytes + lexeme.bytes
        if config.maxBytesPerMention < requiredBytes then
          throw <| .byteBudget (base + offset) requiredBytes config.maxBytesPerMention
        bytes := requiredBytes
        scan := next
        match acceptedValue with
        | some parsed =>
            candidates := candidates + 1
            let globalCandidates := candidateBase + candidates
            if config.maxCandidates < globalCandidates then
              throw <| .candidateBudget globalCandidates config.maxCandidates
            have positive : 0 < width + 1 := by omega
            last := some ⟨width + 1, positive, parsed, candidates⟩
        | none => pure ()
        if terminal then
          return last
  if offset + available < lexemes.size then
    let next := lexemes[offset + available]!.atom
    let continues :=
      match stepAtom config scan next with
      | .next _ _ _ | .valueBudget _ => true
      | .stop => false
    if continues then
      throw <| Error.tokenBudget (base + offset) (available + 1)
        config.maxTokensPerMention
  return last

private def validateRanges (forms : Array String) (ranges : Array (Nat × Nat)) :
    Except Error Unit := do
  for ordinal in [0:ranges.size] do
    let (start, stop) := ranges[ordinal]!
    if stop < start || forms.size < stop then
      throw <| .invalidRange ordinal start stop forms.size

/-- Number of half-open ranges that document normalization will materialize. -/
def documentRangeCount (doc : Doc available) : Nat :=
  if Layer.sents ∈ available then
    doc.sentEnd.size
  else if doc.size = 0 then
    0
  else
    1

/-- Reject an oversized range column at the exact first unit, without traversing it. -/
private def preflightRangeCount (config : Config) (rangeCount : Nat) : Except Error Unit :=
  if config.maxWork < rangeCount then
    .error (.workBudget (config.maxWork + 1) config.maxWork)
  else
    .ok ()

/-- Check document range-allocation work from its layer columns without constructing ranges. -/
def preflightDocumentRangeWorkWith (config : Config) (doc : Doc available) :
    Except Error Unit :=
  preflightRangeCount config (documentRangeCount doc)

private def preflightWork (config : Config) (forms : Array String)
    (ranges : Array (Nat × Nat)) : Except Error Nat := do
  preflightRangeCount config ranges.size
  let mut work := ranges.size
  let mut selectedTokens := 0
  for range in ranges do
    let width := range.2 - range.1
    selectedTokens := selectedTokens + width
    work := work + width * max config.maxTokensPerMention 1
    if config.maxWork < work then
      throw <| .workBudget work config.maxWork
    for index in [range.1:range.2] do
      work := work + forms[index]!.utf8ByteSize + 1
      if config.maxWork < work then
        throw <| .workBudget work config.maxWork
  if config.maxWork < work then
    throw <| .workBudget work config.maxWork
  return selectedTokens

private def lexRange (config : Config) (forms : Array String) (start stop : Nat) :
    Except Error (Array Lexeme) := do
  let mut lexemes := Array.emptyWithCapacity (stop - start)
  for index in [start:stop] do
    lexemes := lexemes.push (← classify config index forms[index]!)
  return lexemes

/-- Normalize ranges already proved valid, sizing output only from selected token positions. -/
private def normalizeCheckedRangesCoreWith (config : Config) (forms : Array String)
    (ranges : Array (Nat × Nat)) : Except Error Result := do
  let selectedTokens ← preflightWork config forms ranges
  let outputBound := min selectedTokens config.maxCandidates
  let capacity := min config.maxMentions outputBound
  let mut mentions : Array (Mention forms ranges) := Array.emptyWithCapacity capacity
  let mut candidateCount := 0
  for hOrdinal : ordinal in [0:ranges.size] do
    have ordinalBound : ordinal < ranges.size := hOrdinal.2.1
    let range := ranges[ordinal]
    let lexemes ← lexRange config forms range.1 range.2
    let mut offset := 0
    for _ in [0:lexemes.size] do
      if lexemes.size ≤ offset then
        break
      match ← longestAt config lexemes range.1 offset candidateCount with
      | none => offset := offset + 1
      | some found =>
          candidateCount := candidateCount + found.candidates
          if config.maxCandidates < candidateCount then
            throw <| .candidateBudget candidateCount config.maxCandidates
          let requiredMentions := mentions.size + 1
          if config.maxMentions < requiredMentions then
            throw <| .mentionBudget requiredMentions config.maxMentions
          let mentionStart := range.1 + offset
          let mentionStop := mentionStart + found.width
          have positive := found.positive
          have nonempty : mentionStart < mentionStop := by
            omega
          if rangeBound : range.2 ≤ forms.size then
            if stopBound : mentionStop ≤ range.2 then
              have startBound : range.1 ≤ mentionStart := by omega
              mentions := mentions.push <|
                .mk ordinal ordinalBound mentionStart mentionStop found.parsed.kind
                  found.parsed.value nonempty startBound stopBound rangeBound
            else
              throw <| .invalidRange ordinal mentionStart mentionStop range.2
          else
            throw <| .invalidRange ordinal range.1 range.2 forms.size
          offset := offset + found.width
  return .mk forms ranges mentions

/--
Extract deterministic longest-leftmost numeric mentions from checked full-input ranges.

Ranges and output coordinates use the original token column. Resource work is conservatively
preflighted before lexeme and output arrays are allocated. Ranges are processed in caller order;
they are normally nonoverlapping sentence ranges from `Doc.sentenceRanges`.
-/
def normalizeRangesWith (config : Config) (forms : Array String)
    (ranges : Array (Nat × Nat)) : Except Error Result := do
  preflightRangeCount config ranges.size
  validateRanges forms ranges
  normalizeCheckedRangesCoreWith config forms ranges

/-- Extract one caller-selected half-open token range under explicit limits. -/
@[inline] def normalizeRangeWith (config : Config) (forms : Array String)
    (start stop : Nat) : Except Error Result :=
  normalizeRangesWith config forms #[(start, stop)]

/-- Extract one caller-selected range with the production resource policy. -/
@[inline] def normalizeRange (forms : Array String) (start stop : Nat) :
    Except Error Result :=
  normalizeRangeWith {} forms start stop

/-- Extract caller-supplied full-input ranges with the production resource policy. -/
@[inline] def normalizeRanges (forms : Array String) (ranges : Array (Nat × Nat)) :
    Except Error Result :=
  normalizeRangesWith {} forms ranges

private structure ReferenceBase where
  value : Rat
  kind : Kind
  rest : List Atom
  requiresScale : Bool := false

private def referenceTens (config : Config) (value : Nat) (ordinal : Bool)
    (rest : List Atom) : Except Nat ReferenceBase := do
  if ordinal then
    return ⟨value, .ordinal, rest, false⟩
  else
    match rest with
    | .hyphen :: .small unit :: tail | .small unit :: tail =>
        if 1 ≤ unit && unit ≤ 9 then
          return ⟨← addRatWith config value unit, .cardinal, tail, false⟩
        else
          return ⟨value, .cardinal, rest, false⟩
    | .hyphen :: .ordinalSmall unit :: tail | .ordinalSmall unit :: tail =>
        if 1 ≤ unit && unit ≤ 9 then
          return ⟨← addRatWith config value unit, .ordinal, tail, false⟩
        else
          return ⟨value, .cardinal, rest, false⟩
    | _ => return ⟨value, .cardinal, rest, false⟩

private def referenceBase (config : Config) (atoms : List Atom) :
    Except Nat (Option ReferenceBase) := do
  match atoms with
  | .small value :: rest => return some ⟨value, .cardinal, rest, false⟩
  | .ordinalSmall value :: rest => return some ⟨value, .ordinal, rest, false⟩
  | .tens value :: rest => return some (← referenceTens config value false rest)
  | .ordinalTens value :: rest => return some (← referenceTens config value true rest)
  | .literal parsed :: rest =>
      return some ⟨parsed.value.rational, parsed.kind, rest, false⟩
  | .indefinite :: rest => return some ⟨1, .cardinal, rest, true⟩
  | _ => return none

private def referenceSeparator : List Atom → Bool × List Atom
  | .comma :: .conjunction :: rest => (true, rest)
  | .comma :: rest | .conjunction :: rest => (true, rest)
  | rest => (false, rest)

private def referenceTail (config : Config) (atoms : List Atom) :
    Except Nat (Option ReferenceBase) := do
  match atoms with
  | .small value :: rest => return some ⟨value, .cardinal, rest, false⟩
  | .ordinalSmall value :: rest => return some ⟨value, .ordinal, rest, false⟩
  | .tens value :: rest => return some (← referenceTens config value false rest)
  | .ordinalTens value :: rest => return some (← referenceTens config value true rest)
  | .literal parsed :: rest =>
      if parsed.kind == .ordinal then
        match smallNonnegative? parsed.value.rational with
        | some value => return some ⟨value, .ordinal, rest, false⟩
        | none => return none
      else
        return none
  | _ => return none

private def referenceGroup (config : Config) (atoms : List Atom) :
    Except Nat (Option ReferenceBase) := do
  let some base ← referenceBase config atoms | return none
  if base.kind == .ordinal then
    return some base
  match base.rest with
  | .ordinalHundred :: rest =>
      if (smallPositive? base.value).isSome then
        return some ⟨← mulRatWith config base.value 100, .ordinal, rest, false⟩
      else
        return none
  | .hundred :: rest =>
      if (smallPositive? base.value).isNone then
        return none
      else
        let value ← mulRatWith config base.value 100
        let (separated, tailAtoms) := referenceSeparator rest
        match ← referenceTail config tailAtoms with
        | some tail =>
            return some ⟨← addRatWith config value tail.value, tail.kind, tail.rest, false⟩
        | none =>
            if separated then return none
            else return some ⟨value, .cardinal, rest, false⟩
  | _ => return some base

private def referenceMagnitude (config : Config) :
    Nat → List Atom → Rat → Nat → Except Nat (Option Parsed)
  | 0, _, _, _ => pure none
  | fuel + 1, atoms, total, lastScale => do
      let some group ← referenceGroup config atoms | return none
      match group.rest with
      | .ordinalScale scale :: rest =>
          if group.kind == .ordinal || group.value == 0 || lastScale ≤ scale ||
              !rest.isEmpty then
            return none
          else
            let scaled ← mulRatWith config group.value scale
            return some ⟨.ordinal, .ofRat (← addRatWith config total scaled)⟩
      | .scale scale :: rest =>
          if group.kind == .ordinal || group.value == 0 || lastScale ≤ scale then
            return none
          else
            let scaled ← mulRatWith config group.value scale
            let nextTotal ← addRatWith config total scaled
            if rest.isEmpty then
              return some ⟨.cardinal, .ofRat nextTotal⟩
            else
              let (separated, tail) := referenceSeparator rest
              if separated && tail.isEmpty then
                return none
              else
                referenceMagnitude config fuel tail nextTotal scale
      | [] =>
          if group.requiresScale then return none
          else return some ⟨group.kind, .ofRat (← addRatWith config total group.value)⟩
      | _ => return none

private def referenceScaleDepth : Nat :=
  5

private def referenceDenote (config : Config) (atoms : List Atom) :
    Except Nat (Option Parsed) := do
  let (negative, signSeen, unsigned) :=
    match atoms with
    | .negative :: rest | .hyphen :: rest => (true, true, rest)
    | .positive :: rest => (false, true, rest)
    | _ => (false, false, atoms)
  let doubleSigned :=
    match unsigned with
    | .literal parsed :: _ => signSeen && parsed.value.rational.num < 0
    | _ => false
  if doubleSigned then
    return none
  else match ← referenceMagnitude config referenceScaleDepth unsigned 0
        1_000_000_000_000_000 with
  | some parsed =>
      if signSeen && parsed.kind == .ordinal then
        return none
      else if negative then
        return some { parsed with value := .ofRat (-parsed.value.rational) }
      else
        return some parsed
  | none => return none

/--
Interpret one complete range with a deliberately separate, slow denotational grammar.

This function shares bounded lexing with production but neither longest-leftmost search nor its
state transition function. Scale recursion has a fixed five-frame cap for the four supported scales.
It is intended as a reference oracle for generated parity tests.
Digit tails after a word tens or hundred phrase are intentionally separate mentions: for example,
`twenty 5` is not one expression, while a digit coefficient before `million` is supported.
-/
def parseReferenceWith (config : Config) (forms : Array String) (start stop : Nat) :
    Except Error Parsed := do
  preflightRangeCount config 1
  let ranges := #[(start, stop)]
  validateRanges forms ranges
  let _ ← preflightWork config forms ranges
  let width := stop - start
  if config.maxTokensPerMention < width then
    throw <| .tokenBudget start width config.maxTokensPerMention
  let mut bytes := 0
  for index in [start:stop] do
    bytes := bytes + forms[index]!.utf8ByteSize
    if config.maxBytesPerMention < bytes then
      throw <| .byteBudget start bytes config.maxBytesPerMention
  let lexemes ← lexRange config forms start stop
  match referenceDenote config (lexemes.toList.map Lexeme.atom) with
  | .error required =>
      throw <| .valueDigitBudget start required config.maxValueDigits
  | .ok (some parsed) =>
      if config.maxCandidates < 1 then
        throw <| .candidateBudget 1 config.maxCandidates
      if config.maxMentions < 1 then
        throw <| .mentionBudget 1 config.maxMentions
      return parsed
  | .ok none => throw <| .notSingleExpression start stop

/-- Interpret one complete range with the production resource policy and reference grammar. -/
@[inline] def parseReference (forms : Array String) (start stop : Nat) : Except Error Parsed :=
  parseReferenceWith {} forms start stop

/--
Parse exactly one selected token range through production longest-leftmost extraction.

The operation succeeds only when extraction yields one mention whose span is the entire selected
range. Use `parseReferenceWith` when an independently implemented test oracle is required.
-/
def parseTokensWith (config : Config) (forms : Array String) (start stop : Nat) :
    Except Error Parsed := do
  match (← normalizeRangeWith config forms start stop).mentions with
  | #[mention] =>
      if mention.start = start && mention.stop = stop then
        return ⟨mention.kind, mention.value⟩
      throw <| .notSingleExpression start stop
  | _ => throw <| .notSingleExpression start stop

/-- Parse exactly one selected range with the production policy. -/
@[inline] def parseTokens (forms : Array String) (start stop : Nat) : Except Error Parsed :=
  parseTokensWith {} forms start stop

/--
Normalize a document whose semantic invariants were already checked by an enclosing boundary.

The explicit witness lets an effectful facade validate length, cancellation, and document
semantics once before invoking this pure normalization layer.
-/
def normalizeCheckedDocumentRangesWith (config : Config) (doc : Doc available)
    (_semantic : doc.SemanticWF) (ranges : Array (Nat × Nat))
    (_ranges_eq : ranges = doc.sentenceRanges)
    (_requirements : Sub [.tokens] available := by decide) : Except Error Result :=
  normalizeCheckedRangesCoreWith config doc.forms ranges

/-- Normalize a semantically checked document after constructing its selected ranges once. -/
def normalizeCheckedDocumentWith (config : Config) (doc : Doc available)
    (semantic : doc.SemanticWF)
    (requirements : Sub [.tokens] available := by decide) : Except Error Result :=
  do
    preflightDocumentRangeWorkWith config doc
    let ranges := doc.sentenceRanges
    normalizeCheckedDocumentRangesWith config doc semantic ranges rfl requirements

/-- Normalize every advertised sentence independently after semantic document validation. -/
def normalizeDocumentWith (config : Config) (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) : Except Error Result :=
  if semantic : doc.SemanticWF then
    normalizeCheckedDocumentWith config doc semantic requirements
  else
    match doc.checkedSemantic with
    | .error cause => .error (.input cause)
    | .ok _ => .error .outputInvariant

/-- Normalize a checked token document with production limits. -/
@[inline] def normalizeDocument (doc : Doc available)
    (requirements : Sub [.tokens] available := by decide) : Except Error Result :=
  normalizeDocumentWith {} doc requirements

end Nlp.Normalize.Numeric
