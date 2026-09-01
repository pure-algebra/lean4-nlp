import Nlp.Normalize.Numeric

/-!
# Exact numeric-normalization regression tests
-/

namespace NlpTests.Normalize.Numeric

open Nlp
open Nlp.Normalize.Numeric

private def parsedAs (result : Except error Parsed) (kind : Kind) (numerator : Int)
    (denominator : Nat := 1) : Bool :=
  match result with
  | .ok parsed =>
      parsed.kind == kind && parsed.value.rational == mkRat numerator denominator
  | .error _ => false

private def parsesAs (source : String) (kind : Kind) (numerator : Int)
    (denominator : Nat := 1) : Bool :=
  parsedAs (parseLiteral source) kind numerator denominator

private def failsWith (result : Except LiteralError Parsed) (expected : LiteralError) : Bool :=
  match result with
  | .error found => decide (found = expected)
  | .ok _ => false

private def extractionFailsWith {α : Type} (result : Except Error α)
    (expected : Error) : Bool :=
  match result with
  | .error found => decide (found = expected)
  | .ok _ => false

private def mentionFacts (result : Result) : Array (Nat × Nat × Kind × Rat) :=
  result.mentions.map fun mention =>
    (mention.start, mention.stop, mention.kind, mention.value.rational)

private def tokenParsesAs (forms : Array String) (kind : Kind) (numerator : Int)
    (denominator : Nat := 1) : Bool :=
  parsedAs (parseTokens forms 0 forms.size) kind numerator denominator

private def referenceParsesAs (forms : Array String) (kind : Kind) (numerator : Int)
    (denominator : Nat := 1) : Bool :=
  parsedAs (parseReference forms 0 forms.size) kind numerator denominator

private def suffixFor (value : Nat) : String :=
  let lastTwo := value % 100
  if lastTwo = 11 || lastTwo = 12 || lastTwo = 13 then
    "th"
  else
    match value % 10 with
    | 1 => "st"
    | 2 => "nd"
    | 3 => "rd"
    | _ => "th"

private def allDigitOrdinals : Bool :=
  (List.range 501).all fun value =>
    parsesAs (toString value ++ suffixFor value) .ordinal value

private def allSmallIntegers : Bool :=
  (List.range 2001).all fun value => parsesAs (toString value) .cardinal value

private def smallWords : Array String :=
  #["zero", "one", "two", "three", "four", "five", "six", "seven", "eight",
    "nine", "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen",
    "sixteen", "seventeen", "eighteen", "nineteen"]

private def tensWords : Array String :=
  #["", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy",
    "eighty", "ninety"]

private def wordsBelowHundred (value : Nat) : Array String :=
  if value < 20 then
    #[smallWords[value]!]
  else if value % 10 = 0 then
    #[tensWords[value / 10]!]
  else
    #[tensWords[value / 10]!, smallWords[value % 10]!]

private def wordsBelowThousand (value : Nat) : Array String :=
  if value < 100 then
    wordsBelowHundred value
  else
    let headWords := #[smallWords[value / 100]!, "hundred"]
    if value % 100 = 0 then headWords
    else headWords ++ #["and"] ++ wordsBelowHundred (value % 100)

private def productionReferenceParity (forms : Array String) : Bool :=
  match parseTokens forms 0 forms.size, parseReference forms 0 forms.size with
  | .ok production, .ok reference => decide (production = reference)
  | _, _ => false

private def allEnglishBelowThousand : Bool :=
  (List.range 1000).all fun value =>
    let forms := wordsBelowThousand value
    productionReferenceParity forms && tokenParsesAs forms .cardinal value

private def longMultipleExponent : String :=
  String.ofList ('1' :: List.replicate 16_384 'e')

#guard parsesAs "-15" .cardinal (-15)
#guard parsesAs "+1,234.50e-2" .cardinal 2469 200
#guard parsesAs "1e3" .cardinal 1000
#guard parsesAs "1E-3" .cardinal 1 1000
#guard parsesAs "0th" .ordinal 0
#guard parsesAs "1,000th" .ordinal 1000
#guard parsesAs "11th" .ordinal 11
#guard parsesAs "22nd" .ordinal 22
#guard allDigitOrdinals
#guard allSmallIntegers

#guard failsWith (parseLiteral "12st") (.invalidOrdinalSuffix "st" 12)
#guard failsWith (parseLiteral "1,23") .invalidGrouping
#guard failsWith (parseLiteral "12,34,567") .invalidGrouping
#guard failsWith (parseLiteral "1.2.3") .invalidSyntax
#guard failsWith (parseLiteral "1e") .invalidSyntax
#guard failsWith (parseLiteral "１２") .invalidSyntax
#guard failsWith (parseLiteral "-1st") .invalidSyntax
#guard failsWith
  (parseLiteralWith { maxBytesPerMention := 16_385 } longMultipleExponent)
  .invalidSyntax

#guard failsWith (parseLiteralWith { maxDigits := 2 } "123") (.digitBudget 3 2)
#guard failsWith (parseLiteralWith { maxDigits := 2 } "1.23") (.digitBudget 3 2)
#guard failsWith (parseLiteralWith { maxDigits := 2 } "1e12") (.digitBudget 3 2)
#guard failsWith (parseLiteralWith { maxExponent := 2 } "1e3") (.exponentBudget 3 2)
#guard parsesAs "123e2" .cardinal 12300
#guard parsedAs (parseLiteralWith { maxValueDigits := 5 } "123e2") .cardinal 12300
#guard failsWith (parseLiteralWith { maxValueDigits := 4 } "123e2")
  (.valueDigitBudget 5 4)
#guard parsedAs (parseLiteralWith { maxValueDigits := 4 } "1e-3") .cardinal 1 1000
#guard failsWith (parseLiteralWith { maxValueDigits := 3 } "1e-3")
  (.valueDigitBudget 4 3)
#guard failsWith (parseLiteralWith { maxValueDigits := 3 } "1e3")
  (.valueDigitBudget 4 3)
#guard parsedAs (parseLiteralWith { maxValueDigits := 4 } "0001e3") .cardinal 1000
#guard failsWith (parseLiteralWith { maxValueDigits := 3 } "0001e3")
  (.valueDigitBudget 4 3)
#guard parsedAs (parseLiteralWith { maxValueDigits := 4 } "0001e-3") .cardinal 1 1000
#guard failsWith (parseLiteralWith { maxValueDigits := 3 } "0001e-3")
  (.valueDigitBudget 4 3)
#guard parsedAs (parseLiteralWith { maxValueDigits := 3 } "123rd") .ordinal 123
#guard failsWith (parseLiteralWith { maxValueDigits := 2 } "123rd")
  (.valueDigitBudget 3 2)
#guard parsedAs (parseLiteralWith { maxValueDigits := 1 } "0e100") .cardinal 0
#guard failsWith (parseLiteralWith { maxValueDigits := 0 } "0e100")
  (.valueDigitBudget 1 0)
#guard parsedAs
  (parseLiteralWith { maxExponent := 1_000_000_000_000, maxValueDigits := 1 }
    "0e1000000000000")
  .cardinal 0
#guard parsedAs
  (parseLiteralWith
    { maxExponent := 1_000_000_000_000, maxValueDigits := 1_000_000_000_001 }
    "0e-1000000000000")
  .cardinal 0
#guard failsWith (parseLiteralWith { maxDigits := 3 } "12e34") (.digitBudget 4 3)
#guard failsWith (parseLiteralWith { maxDigits := 3, maxExponent := 2 } "12e3")
  (.exponentBudget 3 2)

#guard parsedAs (parseTokensWith { maxValueDigits := 3 } #["nine", "hundred"] 0 2)
  .cardinal 900
#guard extractionFailsWith
  (parseTokensWith { maxValueDigits := 2 } #["nine", "hundred"] 0 2)
  (.valueDigitBudget 0 3 2)
#guard parsedAs
  (parseTokensWith { maxValueDigits := 13 } #["nine", "trillion"] 0 2)
  .cardinal 9_000_000_000_000
#guard extractionFailsWith
  (parseTokensWith { maxValueDigits := 12 } #["nine", "trillion"] 0 2)
  (.valueDigitBudget 0 13 12)
#guard parsedAs
  (parseReferenceWith { maxValueDigits := 13 } #["nine", "trillion"] 0 2)
  .cardinal 9_000_000_000_000
#guard extractionFailsWith
  (parseReferenceWith { maxValueDigits := 12 } #["nine", "trillion"] 0 2)
  (.valueDigitBudget 0 13 12)
#guard parsedAs
  (parseTokensWith { maxValueDigits := 7 } #["one", "thousand", "0.001"] 0 3)
  .cardinal 1_000_001 1_000
#guard extractionFailsWith
  (parseTokensWith { maxValueDigits := 6 } #["one", "thousand", "0.001"] 0 3)
  (.valueDigitBudget 0 7 6)
#guard parsedAs
  (parseReferenceWith { maxValueDigits := 7 } #["one", "thousand", "0.001"] 0 3)
  .cardinal 1_000_001 1_000
#guard extractionFailsWith
  (parseReferenceWith { maxValueDigits := 6 } #["one", "thousand", "0.001"] 0 3)
  (.valueDigitBudget 0 7 6)

#guard tokenParsesAs #["twenty", "five"] .cardinal 25
#guard tokenParsesAs #["twenty", "-", "first"] .ordinal 21
#guard tokenParsesAs #["one", "hundred", "and", "fifty", "one"] .cardinal 151
#guard tokenParsesAs #["a", "hundred"] .cardinal 100
#guard tokenParsesAs #["a", "millionth"] .ordinal 1_000_000
#guard referenceParsesAs #["a", "millionth"] .ordinal 1_000_000
#guard tokenParsesAs #["negative", "seven"] .cardinal (-7)
#guard tokenParsesAs #["one", "trillion"] .cardinal 1_000_000_000_000
#guard tokenParsesAs #["one", "million", "two", "thousand", "third"] .ordinal
  1_002_003
#guard tokenParsesAs
  #["4", "million", "six", "hundred", "fifty", "thousand", "two",
    "hundred", "and", "eleven"]
  .cardinal 4_650_211
#guard tokenParsesAs #["1.3", "million"] .cardinal 1_300_000
#guard referenceParsesAs #["one", "million", "two", "thousand", "third"]
  .ordinal 1_002_003
#guard tokenParsesAs #["one", "hundred", "23rd"] .ordinal 123
#guard referenceParsesAs #["one", "hundred", "23rd"] .ordinal 123
#guard allEnglishBelowThousand

#guard extractionFailsWith (parseTokens #["minus", "first"] 0 2)
  (.notSingleExpression 0 2)
#guard extractionFailsWith (parseReference #["minus", "first"] 0 2)
  (.notSingleExpression 0 2)
#guard extractionFailsWith (parseReference #["minus", "-2"] 0 2)
  (.notSingleExpression 0 2)
#guard extractionFailsWith (parseTokens #["one", "hundred", "5"] 0 3)
  (.notSingleExpression 0 3)
#guard extractionFailsWith (parseReference #["twenty", "5"] 0 2)
  (.notSingleExpression 0 2)
#guard extractionFailsWith (parseTokens #["one", "hundred", "123rd"] 0 3)
  (.notSingleExpression 0 3)

#guard
  match normalizeRange #["one", "two", "cats", "first"] 0 4 with
  | .ok result =>
      mentionFacts result ==
        #[(0, 1, .cardinal, 1), (1, 2, .cardinal, 2), (3, 4, .ordinal, 1)]
  | .error _ => false

#guard
  match normalizeRanges #["twenty", "one"] #[(0, 1), (1, 2)] with
  | .ok result =>
      result.source == #["twenty", "one"] && result.ranges == #[(0, 1), (1, 2)] &&
        mentionFacts result == #[(0, 1, .cardinal, 20), (1, 2, .cardinal, 1)]
  | .error _ => false

#guard
  match normalizeRange #["cat", "twenty", "one"] 1 3 with
  | .ok result =>
      match result.mentions with
      | #[mention] =>
          mention.start == 1 && mention.stop == 3 && mention.sourceSize == 3 &&
            mention.rangeStart == 1 && mention.rangeStop == 3
      | _ => false
  | .error _ => false

#guard
  match normalizeRange #["3D", "2ndD", "A320", "three"] 0 4 with
  | .ok result => mentionFacts result == #[(3, 4, .cardinal, 3)]
  | .error _ => false

#guard extractionFailsWith
  (normalizeRangeWith { maxTokensPerMention := 1 } #["twenty", "one"] 0 2)
  (.tokenBudget 0 2 1)
#guard extractionFailsWith
  (normalizeRangeWith { maxTokensPerMention := 2 } #["one", "hundred", "five"] 0 3)
  (.tokenBudget 0 3 2)
#guard extractionFailsWith
  (normalizeRangeWith { maxTokensPerMention := 0 } #["one"] 0 1)
  (.tokenBudget 0 1 0)
#guard extractionFailsWith
  (normalizeRangeWith { maxTokensPerMention := 0 } #["-", "one"] 0 2)
  (.tokenBudget 0 1 0)
#guard
  match normalizeRangeWith { maxTokensPerMention := 1 } #["minus", "first"] 0 2 with
  | .ok result => mentionFacts result == #[(1, 2, .ordinal, 1)]
  | .error _ => false
#guard
  match normalizeRangeWith { maxTokensPerMention := 1 } #["zero", "hundred"] 0 2 with
  | .ok result => mentionFacts result == #[(0, 1, .cardinal, 0)]
  | .error _ => false
#guard
  match normalizeRangeWith { maxTokensPerMention := 3 }
      #["one", "million", "two", "billion"] 0 4 with
  | .ok result => mentionFacts result == #[(0, 3, .cardinal, 1_000_002)]
  | .error _ => false
#guard extractionFailsWith
  (normalizeRangeWith { maxBytesPerMention := 9 } #["one", "hundred"] 0 2)
  (.byteBudget 0 10 9)
#guard
  match normalizeRangeWith { maxBytesPerMention := 10 } #["one", "hundred"] 0 2 with
  | .ok result => result.size == 1
  | .error _ => false
#guard
  match normalizeRangeWith { maxBytesPerMention := 8 } #["one", "twenty"] 0 2 with
  | .ok result =>
      mentionFacts result == #[(0, 1, .cardinal, 1), (1, 2, .cardinal, 20)]
  | .error _ => false
#guard extractionFailsWith
  (normalizeRangeWith { maxBytesPerMention := 2 } #["one"] 0 1)
  (.byteBudget 0 3 2)
#guard extractionFailsWith
  (normalizeRangeWith { maxBytesPerMention := 2 } #["2nd"] 0 1)
  (.literal 0 "2nd" (.byteBudget 3 2))
#guard
  match normalizeRangeWith { maxBytesPerMention := 1 } #["3D"] 0 1 with
  | .ok result => result.size == 0
  | .error _ => false
#guard extractionFailsWith
  (normalizeRangeWith { maxCandidates := 1 } #["one", "cat", "two"] 0 3)
  (.candidateBudget 2 1)
#guard extractionFailsWith
  (normalizeRangesWith { maxCandidates := 1 } #["one", "two"] #[(0, 1), (1, 2)])
  (.candidateBudget 2 1)
#guard extractionFailsWith
  (normalizeRangeWith { maxCandidates := 1 } #["twenty", "one"] 0 2)
  (.candidateBudget 2 1)
#guard extractionFailsWith
  (normalizeRangeWith { maxMentions := 1 } #["one", "cat", "two"] 0 3)
  (.mentionBudget 2 1)
#guard extractionFailsWith
  (normalizeRangeWith { maxWork := 35 } #["one"] 0 1)
  (.workBudget 37 35)
#guard extractionFailsWith
  (normalizeRangeWith { maxWork := 31 } #["one"] 0 1)
  (.workBudget 33 31)
#guard extractionFailsWith (normalizeRanges #["cat", "1e"] #[(1, 2)])
  (.literal 1 "1e" .invalidSyntax)
#guard extractionFailsWith (normalizeRange #["one"] 1 0) (.invalidRange 0 1 0 1)
#guard extractionFailsWith (normalizeRange #["one"] 0 2) (.invalidRange 0 0 2 1)
#guard
  match normalizeRangeWith { maxWork := 37 } #["one"] 0 1 with
  | .ok result => result.size == 1
  | .error _ => false

private def manyEmptyRanges : Array (Nat × Nat) :=
  Array.replicate 4_096 (0, 0)

-- Every selected range costs one unit, even when it selects no token positions.
#guard extractionFailsWith
  (normalizeRangesWith { maxWork := 4_095 } #[] manyEmptyRanges)
  (.workBudget 4_096 4_095)
#guard
  match normalizeRangesWith { maxWork := 4_096 } #[] manyEmptyRanges with
  | .ok result => result.ranges.size == 4_096 && result.mentions.isEmpty
  | .error _ => false

-- The O(1) range-count fence wins before an untrusted range array is traversed.
#guard extractionFailsWith
  (normalizeRangesWith { maxWork := 1 } #[] #[(1, 0), (0, 0)])
  (.workBudget 2 1)
#guard extractionFailsWith
  (normalizeRangesWith { maxWork := 2 } #[] #[(1, 0), (0, 0)])
  (.invalidRange 0 1 0 0)
#guard extractionFailsWith
  (parseReferenceWith { maxWork := 0 } #["one"] 1 0)
  (.workBudget 1 0)
#guard extractionFailsWith
  (parseReferenceWith { maxWork := 1 } #["one"] 1 0)
  (.invalidRange 0 1 0 1)

private def splitTwentyOne : Doc [.sents, .tokens] :=
  { text := "twenty one"
    spans := #[⟨0, 6⟩, ⟨7, 10⟩]
    forms := #["twenty", "one"]
    sentEnd := #[1, 2] }

private def unsplitTwentyOne : Doc [.tokens] :=
  { text := "twenty one"
    spans := #[⟨0, 6⟩, ⟨7, 10⟩]
    forms := #["twenty", "one"] }

private def invalidTokenDocument : Doc [.tokens] :=
  { text := "one", forms := #["one"] }

private def singletonSentenceCount : Nat :=
  256

private def singletonSentences : Doc [.sents, .tokens] :=
  { text := String.ofList (List.replicate singletonSentenceCount 'x')
    spans := (Array.range singletonSentenceCount).map fun index ↦ ⟨index, index + 1⟩
    forms := Array.replicate singletonSentenceCount "one"
    sentEnd := (Array.range singletonSentenceCount).map fun index ↦ index + 1 }

#guard
  match normalizeDocument splitTwentyOne with
  | .ok result =>
      mentionFacts result == #[(0, 1, .cardinal, 20), (1, 2, .cardinal, 1)]
  | .error _ => false

#guard
  match normalizeCheckedDocumentWith {} splitTwentyOne (by native_decide) with
  | .ok result => result.size == 2
  | .error _ => false

#guard
  let ranges := splitTwentyOne.sentenceRanges
  match normalizeCheckedDocumentRangesWith {} splitTwentyOne (by native_decide)
      ranges rfl with
  | .ok result => result.ranges == ranges && result.size == 2
  | .error _ => false

#guard decide singletonSentences.SemanticWF
#guard documentRangeCount singletonSentences == 256
#guard extractionFailsWith
  (preflightDocumentRangeWorkWith { maxWork := 255 } singletonSentences)
  (.workBudget 256 255)
#guard
  match preflightDocumentRangeWorkWith { maxWork := 256 } singletonSentences with
  | .ok _ => true
  | .error _ => false
#guard extractionFailsWith
  (normalizeDocumentWith { maxWork := 255 } singletonSentences)
  (.workBudget 256 255)

-- The checked core independently charges the same range baseline exactly once.
#guard
  let ranges := splitTwentyOne.sentenceRanges
  extractionFailsWith
    (normalizeCheckedDocumentRangesWith { maxWork := 1 } splitTwentyOne
      (by native_decide) ranges rfl)
    (.workBudget 2 1)

#guard
  match normalizeDocument unsplitTwentyOne with
  | .ok result => mentionFacts result == #[(0, 2, .cardinal, 21)]
  | .error _ => false

#guard
  match normalizeDocument invalidTokenDocument with
  | .error (.input _) => true
  | _ => false

example (mention : Mention source ranges) : mention.start < mention.stop :=
  Mention.start_lt_stop mention

example (mention : Mention source ranges) : mention.stop ≤ mention.rangeStop :=
  Mention.stop_le_rangeStop mention

example (mention : Mention source ranges) : mention.stop ≤ mention.sourceSize :=
  Mention.stop_le_sourceSize mention

example (result : Result) (mention : Mention result.source result.ranges)
    (member : mention ∈ result.mentions) :
    mention.stop ≤ result.source.size :=
  Result.mention_stop_le_source result mention member

example (result : Result) (mention : Mention result.source result.ranges)
    (member : mention ∈ result.mentions) :
    (mention.rangeStart, mention.rangeStop) ∈ result.ranges :=
  Result.mention_rangeSelected result mention member

end NlpTests.Normalize.Numeric
