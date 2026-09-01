import Nlp.Pattern.Automaton
import Nlp.Pattern.Token

/-!
# Bounded textual regular expressions over tokens

This module parses a deliberately small textual token-pattern language into the existing
`Regular TokenAtom` kernel. The scanner, predicate parser, and sequence parser use explicit
arrays rather than source-shaped recursion. Flat Boolean and sequence operators are lowered as
balanced trees before the existing recursive evaluators see them.

Core 1 supports exact token-column tests, token-local Boolean composition, concatenation,
alternation, noncapturing groups, and regular quantifiers. Syntax whose meaning needs a tagged or
assertion-aware matcher is rejected explicitly instead of being approximated.
-/

namespace Nlp.Pattern.TokenRegex

open Nlp

/-- A half-open UTF-8 byte span in the exact pattern source. -/
structure ByteSpan where
  /-- Inclusive UTF-8 byte offset. -/
  start : Nat
  /-- Exclusive UTF-8 byte offset. -/
  stop : Nat
  deriving Repr, DecidableEq, Inhabited

/-- TokensRegex features intentionally outside the Core 1 language. -/
inductive UnsupportedFeature where
  /-- Plain or named groups require capture-span semantics. -/
  | capturingGroup
  /-- Sequence anchors require position-sensitive assertion transitions. -/
  | anchor
  /-- Slash-delimited values require a separately bounded character-regex compiler. -/
  | regexLiteral
  /-- Reluctant quantifiers require prioritized path semantics. -/
  | reluctantQuantifier
  /-- Backreferences make matching depend on retained capture values. -/
  | backreference
  /-- Macros require a separately checked environment and expansion phase. -/
  | macro
  /-- Pattern actions and value bindings belong to the staged rule layer. -/
  | action
  deriving Repr, DecidableEq, Inhabited

/-- Resource and syntax reason that textual token-pattern parsing failed. -/
inductive ParseErrorKind where
  /-- The source itself exceeded the UTF-8 byte policy. -/
  | sourceByteBudget (required limit : Nat)
  /-- Scanning needed one more retained lexical item than allowed. -/
  | lexemeBudget (required limit : Nat)
  /-- Delimiter nesting exceeded the effective parser stack policy. -/
  | nestingBudget (required limit : Nat)
  /-- Lowering needed more logical `Regular` constructor occurrences than allowed. -/
  | expandedNodeBudget (required limit : Nat)
  /-- A quoted exact value reached the end of the source. -/
  | unterminatedString
  /-- A quoted exact value used an unsupported escape byte. -/
  | invalidEscape
  /-- The source used a recognized feature outside Core 1. -/
  | unsupported (feature : UnsupportedFeature)
  /-- A token-column name is not part of the typed document schema. -/
  | unknownField (field : String)
  /-- A bounded repetition has its upper bound below its lower bound. -/
  | invertedRepeat (lower upper : Nat)
  /-- The source was empty or contained only whitespace. -/
  | emptyPattern
  /-- The token at the attached byte span did not fit the expected grammar. -/
  | expected (description : String)
  deriving Repr, DecidableEq, Inhabited

/-- One checked parse failure tied to an exact half-open source byte span. -/
structure ParseError where
  /-- Resource or grammar failure. -/
  kind : ParseErrorKind
  /-- Source bytes responsible for the failure. -/
  span : ByteSpan
  deriving Repr, DecidableEq, Inhabited

/-- Resource policy for the iterative textual front end and regular-language lowering. -/
structure ParseConfig where
  /-- Maximum UTF-8 bytes in the complete source. -/
  maxSourceBytes : Nat := 1_048_576
  /-- Maximum non-whitespace lexical items retained by the scanner. -/
  maxLexemes : Nat := 262_144
  /-- Maximum simultaneously open sequence, token, brace, and predicate delimiters. -/
  maxNesting : Nat := 128
  /-- Maximum logical `Regular` constructor occurrences charged during lowering. -/
  maxExpandedNodes : Nat := 262_144
  deriving Repr, DecidableEq, Inhabited

/-- Hard downstream recursion cap even when a caller requests a larger delimiter budget. -/
def hardMaxNesting : Nat := 128

/-- A parsed and resource-checked token language with exact source provenance. -/
structure Pattern where
  private mk ::
  private sourceValue : String
  private regularValue : Regular TokenAtom
  private requirementsValue : Layers
  private expandedNodesValue : Nat

namespace Pattern

/-- Exact textual source retained by a checked pattern. -/
@[inline] def source (pattern : Pattern) : String :=
  pattern.sourceValue

/-- Lowered regular language consumed by the existing reference and automaton modules. -/
@[inline] def language (pattern : Pattern) : Regular TokenAtom :=
  pattern.regularValue

/-- Stable, duplicate-free document layers read by the lowered token predicates. -/
@[inline] def requiredLayers (pattern : Pattern) : Layers :=
  pattern.requirementsValue

/-- Logical regular-constructor occurrences charged while lowering this source. -/
@[inline] def expandedNodeCount (pattern : Pattern) : Nat :=
  pattern.expandedNodesValue

end Pattern

/-- Why checked textual compilation could not produce an existing bounded automaton. -/
inductive CompileError where
  /-- Textual scanning, parsing, or lowering failed. -/
  | parse (cause : ParseError)
  /-- The lowered regular language exceeded the existing Thompson compiler policy. -/
  | automaton (cause : Nlp.Pattern.CompileError)
  deriving Repr, DecidableEq, Inhabited

/-- A checked textual pattern paired with its one-rule existing Thompson automaton. -/
structure Compiled where
  private mk ::
  private patternValue : Pattern
  private automatonValue : Automaton TokenAtom

namespace Compiled

/-- Checked source pattern retained by textual compilation. -/
@[inline] def pattern (compiled : Compiled) : Pattern :=
  compiled.patternValue

/-- Existing one-rule bounded Thompson automaton for the checked pattern. -/
@[inline] def automaton (compiled : Compiled) : Automaton TokenAtom :=
  compiled.automatonValue

/-- Exact textual source retained through automaton compilation. -/
@[inline] def source (compiled : Compiled) : String :=
  compiled.patternValue.source

/-- Document layers required by the compiled token predicates. -/
@[inline] def requiredLayers (compiled : Compiled) : Layers :=
  compiled.patternValue.requiredLayers

end Compiled

private inductive LexemeKind where
  | noncaptureOpen
  | lParen
  | rParen
  | lBracket
  | rBracket
  | lBrace
  | rBrace
  | colon
  | amp
  | pipe
  | bang
  | question
  | star
  | plus
  | comma
  | semicolon
  | exact (value : String)
  | identifier (value : String)
  | number (source : String) (value : Nat) (overflow : Bool)
  deriving Repr, DecidableEq, Inhabited

private structure Lexeme where
  kind : LexemeKind
  span : ByteSpan
  deriving Repr, DecidableEq, Inhabited

@[inline] private def byteAt? (source : String) (index : Nat) : Option UInt8 :=
  if valid : index < source.utf8ByteSize then
    some (source.getUTF8Byte ⟨index⟩ valid)
  else
    none

@[inline] private def ascii (byte : UInt8) : Nat :=
  byte.toNat

@[inline] private def isWhitespaceByte (byte : UInt8) : Bool :=
  ascii byte == 0x20 || ascii byte == 0x09 || ascii byte == 0x0A || ascii byte == 0x0D

@[inline] private def isDigitByte (byte : UInt8) : Bool :=
  0x30 ≤ ascii byte && ascii byte ≤ 0x39

@[inline] private def isAlphaByte (byte : UInt8) : Bool :=
  (0x41 ≤ ascii byte && ascii byte ≤ 0x5A) ||
    (0x61 ≤ ascii byte && ascii byte ≤ 0x7A)

@[inline] private def isIdentifierStart (byte : UInt8) : Bool :=
  isAlphaByte byte || ascii byte == 0x5F

@[inline] private def isIdentifierRest (byte : UInt8) : Bool :=
  isIdentifierStart byte || isDigitByte byte || ascii byte == 0x2E || ascii byte == 0x2D

@[inline] private def sourceSlice (source : String) (start stop : Nat) : String :=
  String.Pos.Raw.extract source ⟨start⟩ ⟨stop⟩

@[inline] private def parseFailure (kind : ParseErrorKind) (span : ByteSpan) :
    Except ParseError α :=
  .error ⟨kind, span⟩

private def scanIdentifierStop (source : String) (start : Nat) : Nat := Id.run do
  let mut stop := start
  for _ in [0:source.utf8ByteSize - start + 1] do
    match byteAt? source stop with
    | some byte =>
        if isIdentifierRest byte then stop := stop + 1 else return stop
    | none => return stop
  return stop

private def scanDigits (config : ParseConfig) (source : String) (start : Nat) :
    Nat × Nat × Bool := Id.run do
  let cap := config.maxExpandedNodes + 1
  let mut stop := start
  let mut value := 0
  let mut overflow := false
  for _ in [0:source.utf8ByteSize - start + 1] do
    match byteAt? source stop with
    | some byte =>
        if isDigitByte byte then
          if !overflow then
            let digit := ascii byte - 0x30
            if value > (cap - digit) / 10 then
              value := cap
              overflow := true
            else
              let next := value * 10 + digit
              if cap < next then
                value := cap
                overflow := true
              else
                value := next
          stop := stop + 1
        else
          return (stop, value, overflow)
    | none => return (stop, value, overflow)
  return (stop, value, overflow)

private def scanQuoted (source : String) (start : Nat) :
    Except ParseError (Lexeme × Nat) := do
  let mut bytes := ByteArray.emptyWithCapacity 0
  let mut cursor := start + 1
  for _ in [0:source.utf8ByteSize - start + 1] do
    match byteAt? source cursor with
    | none =>
        return ← parseFailure .unterminatedString ⟨start, source.utf8ByteSize⟩
    | some byte =>
        if ascii byte == 0x22 then
          match String.fromUTF8? bytes with
          | some value =>
              let stop := cursor + 1
              return (⟨.exact value, ⟨start, stop⟩⟩, stop)
          | none =>
              return ← parseFailure (.expected "valid UTF-8 exact value") ⟨start, cursor⟩
        else if ascii byte == 0x5C then
          match byteAt? source (cursor + 1) with
          | none =>
              return ← parseFailure .unterminatedString ⟨start, source.utf8ByteSize⟩
          | some escaped =>
              let decoded? :=
                match ascii escaped with
                | 0x22 => some (UInt8.ofNat 0x22)
                | 0x5C => some (UInt8.ofNat 0x5C)
                | 0x6E => some (UInt8.ofNat 0x0A)
                | 0x72 => some (UInt8.ofNat 0x0D)
                | 0x74 => some (UInt8.ofNat 0x09)
                | _ => none
              match decoded? with
              | some decoded =>
                  bytes := bytes.push decoded
                  cursor := cursor + 2
              | none =>
                  return ← parseFailure .invalidEscape ⟨cursor, cursor + 2⟩
        else
          bytes := bytes.push byte
          cursor := cursor + 1
  return ← parseFailure .unterminatedString ⟨start, source.utf8ByteSize⟩

private def unsupportedSlashStop (source : String) (start : Nat) : Nat := Id.run do
  let mut cursor := start + 1
  let mut escaped := false
  for _ in [0:source.utf8ByteSize - start + 1] do
    match byteAt? source cursor with
    | none => return source.utf8ByteSize
    | some byte =>
        if escaped then
          escaped := false
          cursor := cursor + 1
        else if ascii byte == 0x5C then
          escaped := true
          cursor := cursor + 1
        else if ascii byte == 0x2F then
          return cursor + 1
        else
          cursor := cursor + 1
  return source.utf8ByteSize

private def scanUnsupportedNameStop (source : String) (start : Nat) : Nat :=
  match byteAt? source (start + 1) with
  | some byte => if isIdentifierStart byte then scanIdentifierStop source (start + 1) else start + 1
  | none => start + 1

private def pushLexeme (config : ParseConfig) (lexemes : Array Lexeme) (lexeme : Lexeme) :
    Except ParseError (Array Lexeme) :=
  if config.maxLexemes < lexemes.size + 1 then
    parseFailure (.lexemeBudget (lexemes.size + 1) config.maxLexemes) lexeme.span
  else
    .ok (lexemes.push lexeme)

private def scan (config : ParseConfig) (source : String) :
    Except ParseError (Array Lexeme) := do
  let size := source.utf8ByteSize
  if config.maxSourceBytes < size then
    return ← parseFailure (.sourceByteBudget size config.maxSourceBytes) ⟨0, size⟩
  let mut lexemes := Array.emptyWithCapacity (min config.maxLexemes (size / 2 + 1))
  let mut cursor := 0
  for _ in [0:size + 1] do
    if size ≤ cursor then
      return lexemes
    let some byte := byteAt? source cursor
      | return lexemes
    if isWhitespaceByte byte then
      cursor := cursor + 1
    else
      let start := cursor
      if config.maxLexemes ≤ lexemes.size then
        return ← parseFailure (.lexemeBudget (lexemes.size + 1) config.maxLexemes)
          ⟨start, min size (start + 1)⟩
      let simple? : Option LexemeKind :=
        match ascii byte with
        | 0x29 => some .rParen
        | 0x5B => some .lBracket
        | 0x5D => some .rBracket
        | 0x7B => some .lBrace
        | 0x7D => some .rBrace
        | 0x3A => some .colon
        | 0x26 => some .amp
        | 0x7C => some .pipe
        | 0x21 => some .bang
        | 0x3F => some .question
        | 0x2A => some .star
        | 0x2B => some .plus
        | 0x2C => some .comma
        | 0x3B => some .semicolon
        | _ => none
      if let some kind := simple? then
        lexemes ← pushLexeme config lexemes ⟨kind, ⟨start, start + 1⟩⟩
        cursor := start + 1
      else match ascii byte with
      | 0x28 =>
          if byteAt? source (start + 1) == some (UInt8.ofNat 0x3F) then
            if byteAt? source (start + 2) == some (UInt8.ofNat 0x3A) then
              lexemes ← pushLexeme config lexemes
                ⟨.noncaptureOpen, ⟨start, start + 3⟩⟩
              cursor := start + 3
            else
              let stop :=
                if byteAt? source (start + 2) == some (UInt8.ofNat 0x24) then
                  scanUnsupportedNameStop source (start + 2)
                else
                  start + 2
              return ← parseFailure (.unsupported .capturingGroup) ⟨start, stop⟩
          else
            lexemes ← pushLexeme config lexemes ⟨.lParen, ⟨start, start + 1⟩⟩
            cursor := start + 1
      | 0x22 =>
          let (lexeme, stop) ← scanQuoted source start
          lexemes ← pushLexeme config lexemes lexeme
          cursor := stop
      | 0x2F =>
          let stop := unsupportedSlashStop source start
          return ← parseFailure (.unsupported .regexLiteral) ⟨start, stop⟩
      | 0x5E =>
          return ← parseFailure (.unsupported .anchor) ⟨start, start + 1⟩
      | 0x24 =>
          let stop := scanUnsupportedNameStop source start
          let feature := if stop == start + 1 then .anchor else .macro
          return ← parseFailure (.unsupported feature) ⟨start, stop⟩
      | 0x5C =>
          let mut stop := start + 1
          for _ in [0:size - start] do
            match byteAt? source stop with
            | some next => if isDigitByte next then stop := stop + 1 else break
            | none => break
          return ← parseFailure (.unsupported .backreference) ⟨start, stop⟩
      | 0x3D =>
          let stop :=
            if byteAt? source (start + 1) == some (UInt8.ofNat 0x3D) &&
                byteAt? source (start + 2) == some (UInt8.ofNat 0x3E) then
              start + 3
            else if byteAt? source (start + 1) == some (UInt8.ofNat 0x3E) then
              start + 2
            else
              start + 1
          if start + 1 < stop then
            return ← parseFailure (.unsupported .action) ⟨start, stop⟩
          else
            return ← parseFailure (.expected "a token-pattern lexical item") ⟨start, stop⟩
      | _ =>
          if isIdentifierStart byte then
            let stop := scanIdentifierStop source start
            let value := sourceSlice source start stop
            lexemes ← pushLexeme config lexemes ⟨.identifier value, ⟨start, stop⟩⟩
            cursor := stop
          else if isDigitByte byte then
            let (stop, value, overflow) := scanDigits config source start
            let raw := sourceSlice source start stop
            lexemes ← pushLexeme config lexemes
              ⟨.number raw value overflow, ⟨start, stop⟩⟩
            cursor := stop
          else
            return ← parseFailure (.expected "ASCII pattern syntax or a quoted exact value")
              ⟨start, start + 1⟩
  return lexemes

@[inline] private def insertLayer (layers : Layers) (layer : Layer) : Layers :=
  if layer ∈ layers then layers else layers ++ [layer]

private def unionLayers (left right : Layers) : Layers :=
  right.foldl insertLayer left

private structure SizedAtom where
  value : TokenAtom
  requirements : Layers
  deriving Inhabited

private inductive NodeCombine where
  | both
  | either

private def combineAtoms (operation : NodeCombine) (items : Array SizedAtom) : SizedAtom :=
  if items.isEmpty then
    ⟨.form .any, [.tokens]⟩
  else Id.run do
    let mut level := items
    for _ in [0:items.size + 1] do
      if level.size ≤ 1 then
        return level[0]!
      let mut next := Array.emptyWithCapacity ((level.size + 1) / 2)
      for pair in [0:(level.size + 1) / 2] do
        let first := pair * 2
        match level[first]?, level[first + 1]? with
        | some left, some right =>
            let value := match operation with
              | .both => TokenAtom.both left.value right.value
              | .either => TokenAtom.either left.value right.value
            next := next.push ⟨value, unionLayers left.requirements right.requirements⟩
        | some left, none => next := next.push left
        | _, _ => pure ()
      level := next
    return level[0]!

private inductive NodeDelimiter where
  | bracket
  | brace
  | paren
  deriving DecidableEq, Inhabited

private structure NodeFrame where
  delimiter : NodeDelimiter
  openSpan : ByteSpan
  negateResult : Bool := false
  terms : Array SizedAtom := #[]
  alternatives : Array SizedAtom := #[]
  expecting : Bool := true
  pendingNegate : Bool := false
  deriving Inhabited

@[inline] private def NodeFrame.toggleNegate (frame : NodeFrame) : NodeFrame :=
  { frame with pendingNegate := !frame.pendingNegate }

@[inline] private def NodeFrame.expectNext (frame : NodeFrame) : NodeFrame :=
  { frame with expecting := true }

@[inline] private def NodeFrame.pushAlternative (frame : NodeFrame)
    (term : SizedAtom) : NodeFrame :=
  { frame with
    terms := #[]
    alternatives := frame.alternatives.push term
    expecting := true }

@[inline] private def NodeFrame.clearPendingNegate (frame : NodeFrame) : NodeFrame :=
  { frame with pendingNegate := false }

@[inline] private def NodeFrame.pushTerm (frame : NodeFrame) (atom : SizedAtom) : NodeFrame :=
  { frame with
    terms := frame.terms.push atom
    expecting := false
    pendingNegate := false }

private def finishNodeFrame (frame : NodeFrame) : Except ParseError SizedAtom := do
  if frame.expecting || frame.terms.isEmpty then
    return ← parseFailure (.expected "a token predicate") frame.openSpan
  let term := combineAtoms .both frame.terms
  let choices := frame.alternatives.push term
  let result := combineAtoms .either choices
  if frame.negateResult then
    return ⟨.negate result.value, result.requirements⟩
  return result

private def primitiveAtom (field value : String) (span : ByteSpan) :
    Except ParseError SizedAtom :=
  match field with
  | "word" | "form" => .ok ⟨.form (.equal value), [.tokens]⟩
  | "tag" | "pos" => .ok ⟨.pos (.equal value), [.tokens, .pos]⟩
  | "lemma" => .ok ⟨.lemma (.equal value), [.tokens, .lemma]⟩
  | "ner" => .ok ⟨.ner (.equal value), [.tokens, .ner]⟩
  | _ => parseFailure (.unknownField field) span

private def exactValue? : LexemeKind → Option String
  | .exact value | .identifier value => some value
  | .number source _ _ => some source
  | _ => none

private def effectiveNesting (config : ParseConfig) : Nat :=
  min config.maxNesting hardMaxNesting

private def parseNode (config : ParseConfig) (lexemes : Array Lexeme) (start : Nat)
    (sequenceDepth : Nat) : Except ParseError (SizedAtom × Nat) := do
  let some opener := lexemes[start]? |
    return ← parseFailure (.expected "`[`") ⟨0, 0⟩
  let limit := effectiveNesting config
  let bracketDepth := sequenceDepth + 1
  if limit < bracketDepth then
    return ← parseFailure (.nestingBudget bracketDepth limit) opener.span
  let mut parents : Array NodeFrame := #[]
  let mut frame : NodeFrame := { delimiter := .bracket, openSpan := opener.span }
  let mut cursor := start + 1
  for _ in [0:lexemes.size - start + 1] do
    let some lexeme := lexemes[cursor]? |
      return ← parseFailure (.expected "`]`") ⟨opener.span.stop, opener.span.stop⟩
    match lexeme.kind with
    | .rBracket =>
        if !parents.isEmpty then
          return ← parseFailure (.expected "the open predicate delimiter") lexeme.span
        if frame.expecting && frame.terms.isEmpty && frame.alternatives.isEmpty then
          return (⟨.form .any, [.tokens]⟩, cursor + 1)
        let result ← finishNodeFrame frame
        return (result, cursor + 1)
    | .bang =>
        if !frame.expecting then
          return ← parseFailure (.expected "`&`, `|`, or `]`") lexeme.span
        frame := frame.toggleNegate
        cursor := cursor + 1
    | .amp | .semicolon =>
        if frame.expecting then
          return ← parseFailure (.expected "a token predicate before conjunction") lexeme.span
        frame := frame.expectNext
        cursor := cursor + 1
    | .pipe =>
        if frame.expecting || frame.terms.isEmpty then
          return ← parseFailure (.expected "a token predicate before `|`") lexeme.span
        let term := combineAtoms .both frame.terms
        frame := frame.pushAlternative term
        cursor := cursor + 1
    | .lBrace | .lParen =>
        if !frame.expecting then
          return ← parseFailure (.expected "`&`, `|`, or `]`") lexeme.span
        let required := sequenceDepth + parents.size + 2
        if limit < required then
          return ← parseFailure (.nestingBudget required limit) lexeme.span
        let negateResult := frame.pendingNegate
        frame := frame.clearPendingNegate
        parents := parents.push frame
        let delimiter := match lexeme.kind with
          | .lBrace => NodeDelimiter.brace
          | _ => NodeDelimiter.paren
        frame :=
          { delimiter := delimiter
            openSpan := lexeme.span
            negateResult := negateResult }
        cursor := cursor + 1
    | .rBrace | .rParen =>
        if parents.isEmpty then
          return ← parseFailure (.expected "a matching predicate opener") lexeme.span
        let expected := match lexeme.kind with
          | .rBrace => NodeDelimiter.brace
          | _ => NodeDelimiter.paren
        if frame.delimiter != expected then
          return ← parseFailure (.expected "the matching predicate closer") lexeme.span
        let result ← finishNodeFrame frame
        let parent := parents.back!
        parents := parents.pop
        if !parent.expecting then
          return ← parseFailure (.expected "`&`, `|`, or `]`") lexeme.span
        frame := parent.pushTerm result
        cursor := cursor + 1
    | .identifier field =>
        if !frame.expecting then
          return ← parseFailure (.expected "`&`, `|`, or `]`") lexeme.span
        let some colon := lexemes[cursor + 1]? |
          return ← parseFailure (.expected "`:` after a token field") lexeme.span
        unless colon.kind == .colon do
          return ← parseFailure (.expected "`:` after a token field") colon.span
        let some valueLexeme := lexemes[cursor + 2]? |
          return ← parseFailure (.expected "an exact field value") colon.span
        let some value := exactValue? valueLexeme.kind |
          return ← parseFailure (.expected "a quoted or bare exact field value") valueLexeme.span
        let atom ← primitiveAtom field value lexeme.span
        let atom := if frame.pendingNegate then
          { atom with value := .negate atom.value }
        else atom
        frame := frame.pushTerm atom
        cursor := cursor + 3
    | _ =>
        return ← parseFailure (.expected "a token-local exact predicate") lexeme.span
  return ← parseFailure (.expected "`]`") opener.span

private structure SizedRegular where
  value : Regular TokenAtom
  nodes : Nat
  requirements : Layers

private instance : Inhabited SizedRegular :=
  ⟨⟨.empty, 1, []⟩⟩

private structure LowerState where
  used : Nat := 0

private def reserveNodes (config : ParseConfig) (state : LowerState) (amount : Nat)
    (span : ByteSpan) : Except ParseError LowerState :=
  let remaining := config.maxExpandedNodes - state.used
  if remaining < amount then
    parseFailure (.expandedNodeBudget (config.maxExpandedNodes + 1)
      config.maxExpandedNodes) span
  else
    .ok ⟨state.used + amount⟩

private inductive RegularCombine where
  | seq
  | alt

private def combineRegularsUnchecked (operation : RegularCombine)
    (items : Array SizedRegular) : SizedRegular :=
  if items.isEmpty then
    ⟨.epsilon, 1, []⟩
  else Id.run do
    let mut level := items
    for _ in [0:items.size + 1] do
      if level.size ≤ 1 then
        return level[0]!
      let mut next := Array.emptyWithCapacity ((level.size + 1) / 2)
      for pair in [0:(level.size + 1) / 2] do
        let first := pair * 2
        match level[first]?, level[first + 1]? with
        | some left, some right =>
            let value := match operation with
              | .seq => Regular.seq left.value right.value
              | .alt => Regular.alt left.value right.value
            next := next.push
              ⟨value, left.nodes + right.nodes + 1,
                unionLayers left.requirements right.requirements⟩
        | some left, none => next := next.push left
        | _, _ => pure ()
      level := next
    return level[0]!

private def combineRegulars (config : ParseConfig) (state : LowerState)
    (operation : RegularCombine) (items : Array SizedRegular) (span : ByteSpan) :
    Except ParseError (LowerState × SizedRegular) := do
  if items.isEmpty then
    let state ← reserveNodes config state 1 span
    return (state, ⟨.epsilon, 1, []⟩)
  let connectors := items.size - 1
  let state ← reserveNodes config state connectors span
  return (state, combineRegularsUnchecked operation items)

private structure SequenceFrame where
  openSpan : ByteSpan
  parts : Array SizedRegular := #[]
  alternatives : Array SizedRegular := #[]
  expecting : Bool := true
  quantified : Bool := false
  deriving Inhabited

@[inline] private def SequenceFrame.pushPart (frame : SequenceFrame)
    (part : SizedRegular) : SequenceFrame :=
  { frame with
    parts := frame.parts.push part
    expecting := false
    quantified := false }

@[inline] private def SequenceFrame.pushAlternative (frame : SequenceFrame)
    (term : SizedRegular) : SequenceFrame :=
  { frame with
    parts := #[]
    alternatives := frame.alternatives.push term
    expecting := true
    quantified := false }

@[inline] private def SequenceFrame.replaceLast (frame : SequenceFrame)
    (part : SizedRegular) : SequenceFrame :=
  { frame with parts := frame.parts.pop.push part, quantified := true }

private def finishSequenceFrame (config : ParseConfig) (state : LowerState)
    (frame : SequenceFrame) : Except ParseError (LowerState × SizedRegular) := do
  if frame.expecting || frame.parts.isEmpty then
    return ← parseFailure (.expected "a token sequence") frame.openSpan
  let (state, term) ← combineRegulars config state .seq frame.parts frame.openSpan
  combineRegulars config state .alt (frame.alternatives.push term) frame.openSpan

private inductive RepeatSpec where
  | optional
  | star
  | plus
  | finite (lower upper : Nat)
  | unbounded (lower : Nat)

private def cappedMul (limit left right : Nat) : Nat :=
  if left == 0 || right == 0 then 0
  else if limit / left < right then limit + 1
  else left * right

private def cappedAdd (limit left right : Nat) : Nat :=
  if limit - min left limit < right then limit + 1 else left + right

private def repeatExtra (limit : Nat) (bodyNodes : Nat) : RepeatSpec → Nat
  | .optional => 2
  | .star => 1
  | .plus => cappedAdd limit bodyNodes 2
  | .finite lower upper =>
      if upper == 0 then 1
      else
        let copies := cappedMul limit (upper - 1) bodyNodes
        let optionals := cappedMul limit 2 (upper - lower)
        cappedAdd limit (cappedAdd limit copies optionals) (upper - 1)
  | .unbounded lower =>
      let copies := cappedMul limit lower bodyNodes
      cappedAdd limit (cappedAdd limit copies 1) lower

private def repeatedItems (body : SizedRegular) (count : Nat) : Array SizedRegular := Id.run do
  let mut output := Array.emptyWithCapacity count
  for _ in [0:count] do
    output := output.push body
  return output

private def applyRepeat (config : ParseConfig) (state : LowerState) (body : SizedRegular)
    (spec : RepeatSpec) (span : ByteSpan) : Except ParseError (LowerState × SizedRegular) := do
  let extra := repeatExtra config.maxExpandedNodes body.nodes spec
  let state ← reserveNodes config state extra span
  match spec with
  | .optional =>
      return (state,
        ⟨.alt body.value .epsilon, body.nodes + 2, body.requirements⟩)
  | .star =>
      return (state, ⟨.star body.value, body.nodes + 1, body.requirements⟩)
  | .plus =>
      return (state,
        ⟨.seq body.value (.star body.value), 2 * body.nodes + 2, body.requirements⟩)
  | .finite lower upper =>
      if upper == 0 then
        return (state, ⟨.epsilon, 1, []⟩)
      let mut items := repeatedItems body lower
      for _ in [lower:upper] do
        items := items.push
          ⟨.alt body.value .epsilon, body.nodes + 2, body.requirements⟩
      return (state, combineRegularsUnchecked .seq items)
  | .unbounded lower =>
      let mut items := repeatedItems body lower
      items := items.push ⟨.star body.value, body.nodes + 1, body.requirements⟩
      return (state, combineRegularsUnchecked .seq items)

private def reluctantAt? (lexemes : Array Lexeme) (index : Nat) : Option ByteSpan :=
  match lexemes[index]?, lexemes[index + 1]? with
  | some first, some second =>
      let quantifier := match first.kind with
        | .question | .star | .plus => true
        | _ => false
      if quantifier && second.kind == .question then
        some ⟨first.span.start, second.span.stop⟩
      else none
  | _, _ => none

private def parseBoundedRepeat (config : ParseConfig) (lexemes : Array Lexeme)
    (index : Nat) : Except ParseError (RepeatSpec × Nat × ByteSpan) := do
  let opener := lexemes[index]!
  let some lowerLexeme := lexemes[index + 1]? |
    return ← parseFailure (.expected "a decimal repetition lower bound") opener.span
  let .number _ lower overflow := lowerLexeme.kind
    | return ← parseFailure (.expected "a decimal repetition lower bound") lowerLexeme.span
  if overflow then
    return ← parseFailure
      (.expandedNodeBudget (config.maxExpandedNodes + 1) config.maxExpandedNodes)
      lowerLexeme.span
  let some separator := lexemes[index + 2]? |
    return ← parseFailure (.expected "`,` or `}` in a repetition") lowerLexeme.span
  match separator.kind with
  | .rBrace =>
      let next := index + 3
      match lexemes[next]? with
      | some reluctant =>
          if reluctant.kind == .question then
            return ← parseFailure (.unsupported .reluctantQuantifier)
              ⟨opener.span.start, reluctant.span.stop⟩
      | none => pure ()
      return (.finite lower lower, next, ⟨opener.span.start, separator.span.stop⟩)
  | .comma =>
      let some upperLexeme := lexemes[index + 3]? |
        return ← parseFailure (.expected "a decimal upper bound or `}`") separator.span
      match upperLexeme.kind with
      | .rBrace =>
          let next := index + 4
          match lexemes[next]? with
          | some reluctant =>
              if reluctant.kind == .question then
                return ← parseFailure (.unsupported .reluctantQuantifier)
                  ⟨opener.span.start, reluctant.span.stop⟩
          | none => pure ()
          return (.unbounded lower, next, ⟨opener.span.start, upperLexeme.span.stop⟩)
      | .number _ upper upperOverflow =>
          if upperOverflow then
            return ← parseFailure
              (.expandedNodeBudget (config.maxExpandedNodes + 1) config.maxExpandedNodes)
              upperLexeme.span
          let some closer := lexemes[index + 4]? |
            return ← parseFailure (.expected "`}` after a repetition upper bound")
              upperLexeme.span
          unless closer.kind == .rBrace do
            return ← parseFailure (.expected "`}` after a repetition upper bound") closer.span
          if upper < lower then
            return ← parseFailure (.invertedRepeat lower upper)
              ⟨opener.span.start, closer.span.stop⟩
          let next := index + 5
          match lexemes[next]? with
          | some reluctant =>
              if reluctant.kind == .question then
                return ← parseFailure (.unsupported .reluctantQuantifier)
                  ⟨opener.span.start, reluctant.span.stop⟩
          | none => pure ()
          return (.finite lower upper, next, ⟨opener.span.start, closer.span.stop⟩)
      | _ =>
          return ← parseFailure (.expected "a decimal upper bound or `}`") upperLexeme.span
  | _ =>
      return ← parseFailure (.expected "`,` or `}` in a repetition") separator.span

private def parseSequence (config : ParseConfig) (source : String)
    (lexemes : Array Lexeme) : Except ParseError Pattern := do
  if lexemes.isEmpty then
    return ← parseFailure .emptyPattern ⟨0, source.utf8ByteSize⟩
  let eof : ByteSpan := ⟨source.utf8ByteSize, source.utf8ByteSize⟩
  let mut parents : Array SequenceFrame := #[]
  let mut frame : SequenceFrame := { openSpan := ⟨0, 0⟩ }
  let mut lower : LowerState := {}
  let mut cursor := 0
  for _ in [0:lexemes.size + 1] do
    if lexemes.size ≤ cursor then
      if !parents.isEmpty then
        return ← parseFailure (.expected "`)`") frame.openSpan
      let (nextLower, result) ← finishSequenceFrame config lower frame
      lower := nextLower
      return .mk source result.value result.requirements lower.used
    let lexeme := lexemes[cursor]!
    match lexeme.kind with
    | .lBracket =>
        let (atom, next) ← parseNode config lexemes cursor parents.size
        lower ← reserveNodes config lower 1 lexeme.span
        let regular : SizedRegular := ⟨.atom atom.value, 1, atom.requirements⟩
        frame := frame.pushPart regular
        cursor := next
    | .noncaptureOpen =>
        let required := parents.size + 1
        let limit := effectiveNesting config
        if limit < required then
          return ← parseFailure (.nestingBudget required limit) lexeme.span
        parents := parents.push frame
        frame := { openSpan := lexeme.span }
        cursor := cursor + 1
    | .lParen =>
        return ← parseFailure (.unsupported .capturingGroup) lexeme.span
    | .rParen =>
        if parents.isEmpty then
          return ← parseFailure (.expected "a matching `(?:`") lexeme.span
        let (nextLower, result) ← finishSequenceFrame config lower frame
        lower := nextLower
        let parent := parents.back!
        parents := parents.pop
        frame := parent.pushPart result
        cursor := cursor + 1
    | .pipe =>
        if frame.expecting || frame.parts.isEmpty then
          return ← parseFailure (.expected "a sequence before `|`") lexeme.span
        let (nextLower, term) ← combineRegulars config lower .seq frame.parts lexeme.span
        lower := nextLower
        frame := frame.pushAlternative term
        cursor := cursor + 1
    | .question | .star | .plus =>
        if frame.expecting || frame.parts.isEmpty || frame.quantified then
          return ← parseFailure (.expected "one unquantified sequence expression") lexeme.span
        match reluctantAt? lexemes cursor with
        | some span =>
            return ← parseFailure (.unsupported .reluctantQuantifier) span
        | none => pure ()
        let spec := match lexeme.kind with
          | .question => RepeatSpec.optional
          | .star => RepeatSpec.star
          | _ => RepeatSpec.plus
        let body := frame.parts.back!
        let (nextLower, repeated) ← applyRepeat config lower body spec lexeme.span
        lower := nextLower
        frame := frame.replaceLast repeated
        cursor := cursor + 1
    | .lBrace =>
        if frame.expecting || frame.parts.isEmpty || frame.quantified then
          return ← parseFailure (.expected "one unquantified sequence expression") lexeme.span
        let (spec, next, span) ← parseBoundedRepeat config lexemes cursor
        let body := frame.parts.back!
        let (nextLower, repeated) ← applyRepeat config lower body spec span
        lower := nextLower
        frame := frame.replaceLast repeated
        cursor := next
    | _ =>
        return ← parseFailure (.expected "a token test, sequence operator, or quantifier")
          lexeme.span
  return ← parseFailure (.expected "end of pattern") eof

/-- Parse and lower one textual token language under explicit front-end resource policies. -/
def parseWith (config : ParseConfig) (source : String) : Except ParseError Pattern := do
  let lexemes ← scan config source
  parseSequence config source lexemes

/-- Parse and lower one textual token language with the default resource policies. -/
@[inline] def parse (source : String) : Except ParseError Pattern :=
  parseWith {} source

/--
Parse one textual token language and compile it as rule zero in the existing bounded automaton.

The returned wrapper retains the exact source and checked document-layer requirements; no
textual validation is repeated by consumers of the compiled value.
-/
def compileWith (parseConfig : ParseConfig) (automatonConfig : Nlp.Pattern.CompileConfig)
    (source : String) : Except CompileError Compiled := do
  let pattern ←
    match parseWith parseConfig source with
    | .ok value => pure value
    | .error cause => throw <| .parse cause
  let automaton ←
    match Automaton.compileWith automatonConfig #[pattern.language] with
    | .ok value => pure value
    | .error cause => throw <| .automaton cause
  return .mk pattern automaton

/-- Parse and compile one textual token language with both default resource policies. -/
@[inline] def compile (source : String) : Except CompileError Compiled :=
  compileWith {} {} source

/-- Why a compiled textual pattern could not be matched against one document. -/
inductive MatchError where
  /-- The document failed the ordinary semantic boundary. -/
  | input (cause : Doc.SemanticError)
  /-- The document does not advertise one column required by the source pattern. -/
  | missingLayer (layer : Layer)
  /-- The existing bounded automaton rejected its work or result policy. -/
  | search (cause : Nlp.Pattern.SearchError)
  deriving Repr, DecidableEq, Inhabited

namespace Compiled

/-- First dynamically required document column not advertised by `available`, if any. -/
def missingLayer? (compiled : Compiled) (available : Layers) : Option Layer :=
  compiled.requiredLayers.find? fun layer ↦ decide (layer ∉ available)

/--
Find every nonempty match after validating the document and required annotation columns once.

The hot loop uses `TokenAtom.holdsAtUnchecked` only after those checks, avoiding a repeated dynamic
layer-set scan at every NFA transition. Coordinates remain absolute document token positions.
-/
def findOverlappingRangeWith (compiled : Compiled) (config : Nlp.Pattern.SearchConfig)
    (doc : Doc available) (start : Nat := 0) (stop : Nat := doc.size) :
    Except MatchError (Array Nlp.Pattern.Match) := do
  let checked ←
    match doc.checkedSemantic with
    | .ok value => pure value
    | .error cause => throw <| .input cause
  if let some layer := compiled.missingLayer? available then
    throw <| .missingLayer layer
  let found := compiled.automaton.findOverlappingRangeWith config
    (TokenAtom.holdsAtUnchecked checked) checked.size start stop
  match found with
  | .ok foundMatches => return foundMatches
  | .error cause => throw <| .search cause

/-- Match with the production automaton search limits. -/
@[inline] def findOverlappingRange (compiled : Compiled) (doc : Doc available)
    (start : Nat := 0) (stop : Nat := doc.size) : Except MatchError (Array Nlp.Pattern.Match) :=
  compiled.findOverlappingRangeWith {} doc start stop

end Compiled

end Nlp.Pattern.TokenRegex
