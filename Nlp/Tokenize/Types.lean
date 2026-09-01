import Nlp.Core.Data.Span

/-!
# Tokenizer values and configuration

The tokenizer keeps positions as `String.Pos` values until a caller asks for the public UTF-8 byte
span. This makes every emitted boundary valid for the exact source string by construction. Token
forms are source slices rather than separately normalized strings, while `Tokenization` retains
the original text for exact source recovery.
-/

namespace Nlp.Tokenize

/-- The scanner used to find token boundaries. -/
inductive Mode where
  /-- Split at maximal runs of Unicode whitespace and otherwise retain each maximal source run. -/
  | whitespace
  /-- Apply the dependency-free English/UD-oriented lexical rules. -/
  | englishUD
  deriving Repr, DecidableEq, Inhabited

/-- A coarse lexical class suitable for downstream rule dispatch and diagnostics. -/
inductive TokenKind where
  | word
  | number
  | punctuation
  | symbol
  | newline
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Total tokenizer options; every combination has deterministic semantics. -/
structure Config where
  mode : Mode := .englishUD
  /-- Emit each logical line break, with CRLF retained as one token, instead of discarding it. -/
  keepNewlines : Bool := false
  /-- In English/UD mode, split an in-word hyphen into a punctuation token. -/
  splitHyphenated : Bool := true
  /-- In English/UD mode, split an in-word forward slash into a punctuation token. -/
  splitForwardSlash : Bool := true
  /-- Split productive English apostrophe contractions such as `isn't` and `they've`. -/
  splitContractions : Bool := true
  /-- Split the finite treebank assimilation set, including `gonna`, `wanna`, and `cannot`. -/
  splitAssimilations : Bool := true
  deriving Repr, DecidableEq, Inhabited

/-- One nonempty token whose boundaries are valid positions in `text` and occur in source order. -/
structure Token (text : String) where
  private mk ::
  startPos : text.Pos
  endPos : text.Pos
  nonempty : startPos < endPos
  kind : TokenKind

namespace Token

/-- Construct a nonempty token from strictly ordered, source-indexed positions. -/
@[inline] def ofPositions (startPos endPos : text.Pos) (nonempty : startPos < endPos)
    (kind : TokenKind) : Token text :=
  ⟨startPos, endPos, nonempty, kind⟩

/-- The public half-open UTF-8 byte span of a token. -/
@[inline] def span (token : Token text) : Span :=
  ⟨token.startPos.offset.byteIdx, token.endPos.offset.byteIdx⟩

/-- Recover the token's exact original spelling from its source positions. -/
@[inline] def original (token : Token text) : String :=
  text.extract token.startPos token.endPos

/-- Every token span is ordered. -/
theorem span_wf (token : Token text) : token.span.WF := by
  exact Nat.le_of_lt (String.Pos.Raw.lt_iff.mp (String.Pos.lt_iff.mp token.nonempty))

/-- Every token occupies at least one UTF-8 byte. -/
theorem span_nonempty (token : Token text) : token.span.b < token.span.e := by
  exact String.Pos.Raw.lt_iff.mp (String.Pos.lt_iff.mp token.nonempty)

/-- Every token begins within its source string. -/
theorem span_begin_le_source (token : Token text) : token.span.b ≤ text.utf8ByteSize := by
  exact token.startPos.isValid.le_utf8ByteSize

/-- Every token ends within its source string. -/
theorem span_end_le_source (token : Token text) : token.span.e ≤ text.utf8ByteSize := by
  exact token.endPos.isValid.le_utf8ByteSize

end Token

/-- A token sequence tied to the exact string from which all of its positions were derived. -/
structure Tokenization where
  text : String
  tokens : Array (Token text)

namespace Tokenization

/-- Number of emitted tokens. -/
@[inline] def size (tokenization : Tokenization) : Nat := tokenization.tokens.size

/-- Executably check adjacent spans; transitivity orders every later token as well. -/
def ordered {text : String} : List (Token text) → Bool
  | [] | [_] => true
  | left :: right :: rest =>
      decide (left.endPos ≤ right.startPos) && ordered (right :: rest)

/-- Tokens are nonoverlapping and occur in strictly increasing source order. -/
def WF (tokenization : Tokenization) : Prop :=
  ordered tokenization.tokens.toList = true

instance (tokenization : Tokenization) : Decidable tokenization.WF := by
  unfold WF
  infer_instance

/-- Executable form of `Tokenization.WF` for validation boundaries and property tests. -/
@[inline] def isWF (tokenization : Tokenization) : Bool :=
  ordered tokenization.tokens.toList

/-- Materialize the struct-of-arrays span column expected by `Nlp.Doc`. -/
def spans (tokenization : Tokenization) : Array Span :=
  tokenization.tokens.map Token.span

/-- Materialize exact source spellings for the `Nlp.Doc` form column. -/
def forms (tokenization : Tokenization) : Array String :=
  tokenization.tokens.map Token.original

/-- Materialize coarse lexical classes in token order. -/
def kinds (tokenization : Tokenization) : Array TokenKind :=
  tokenization.tokens.map Token.kind

/-- Recover the exact original spelling of a token, when the index exists. -/
@[inline] def originalAt (tokenization : Tokenization) (index : Nat) : Option String :=
  tokenization.tokens[index]?.map Token.original

/-- Read a token's byte span, when the index exists. -/
@[inline] def spanAt (tokenization : Tokenization) (index : Nat) : Option Span :=
  tokenization.tokens[index]?.map Token.span

/-- Read a token's coarse class, when the index exists. -/
@[inline] def kindAt (tokenization : Tokenization) (index : Nat) : Option TokenKind :=
  tokenization.tokens[index]?.map Token.kind

end Tokenization

end Nlp.Tokenize
