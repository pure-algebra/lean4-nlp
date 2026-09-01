import Nlp.Tokenize.Types

/-!
# Deterministic sentence splitting

Sentence boundaries are stored as exclusive token indices into the exact `Tokenization` supplied
by the caller.  The splitter scans the token array once.  Source gaps and emitted newline tokens
are inspected through `String.Pos`-bounded slices, so detecting line breaks does not allocate gap
substrings.

Rule priority is explicit:

1. `oneSentence` ignores every other option and emits one sentence exactly when tokens exist.
2. In the other modes, an enabled newline boundary closes the preceding nonempty token range.
3. In `rules`, adjacent sentence-final punctuation is one run.  Immediately following closing
   quotes and brackets remain attached to that run; the boundary is emitted before the next token.
4. End of input closes the final nonempty range.  Duplicate and empty boundaries are discarded.

For caller-built tokenizations, a source gap is inspected only when the previous token end does not
follow the current token start.  Reordered and overlapping tokens therefore remain total inputs and
still produce well-formed token-index boundaries, although their textual order has no linguistic
interpretation.
-/

namespace Nlp.Tokenize.Sentence

/-- Which evidence is allowed to terminate a sentence. -/
inductive Mode where
  /-- Use sentence-final punctuation together with the configured newline policy. -/
  | rules
  /-- Return the entire nonempty tokenization as one sentence. -/
  | oneSentence
  /-- Ignore punctuation and split at every logical line break. -/
  | eolOnly
  deriving Repr, DecidableEq, Inhabited

/-- How logical line breaks participate in sentence boundaries. -/
inductive NewlinePolicy where
  /-- Ignore line breaks. -/
  | never
  /-- Every logical line break is a boundary. -/
  | always
  /-- Two consecutive logical line breaks are a boundary. -/
  | two
  deriving Repr, DecidableEq, Inhabited

/-- Total sentence-splitting options; every mode/policy combination has defined behavior. -/
structure Config where
  mode : Mode := .rules
  newlinePolicy : NewlinePolicy := .never
  deriving Repr, DecidableEq, Inhabited

/-- A source tokenization together with exclusive token-index sentence ends. -/
structure Segmentation where
  source : Tokenization
  ends : Array Nat

namespace Segmentation

/--
Sentence ends are nonzero, bounded by the token count, and strictly increasing.  Empty input has
no sentence; nonempty input has a final boundary at the token count.
-/
def WF (segmentation : Segmentation) : Prop :=
  segmentation.ends.toList.Pairwise (fun left right => left < right) ∧
    (∀ endExclusive ∈ segmentation.ends.toList,
      0 < endExclusive ∧ endExclusive ≤ segmentation.source.size) ∧
    (segmentation.ends.toList = [] ↔ segmentation.source.size = 0) ∧
    (0 < segmentation.source.size →
      segmentation.ends.toList.getLast? = some segmentation.source.size)

/-- Number of sentences represented by the exclusive ends. -/
@[inline] def size (segmentation : Segmentation) : Nat := segmentation.ends.size

/-- The half-open token-index range of a sentence, when that sentence exists. -/
def rangeAt? (segmentation : Segmentation) (sentence : Nat) : Option (Nat × Nat) := do
  let stop ← segmentation.ends[sentence]?
  let start ← if sentence = 0 then some 0 else segmentation.ends[sentence - 1]?
  pure (start, stop)

end Segmentation

private structure NewlineScan where
  count : Nat := 0
  previousCR : Bool := false

/-- Counts are saturated because policies distinguish only zero, one, and at least two breaks. -/
@[inline] private def NewlineScan.bump (scan : NewlineScan) : NewlineScan :=
  { scan with count := min 2 (scan.count + 1) }

@[inline] private def NewlineScan.step (scan : NewlineScan) (character : Char) : NewlineScan :=
  let code := character.toNat
  if character == '\r' then
    { scan.bump with previousCR := true }
  else if character == '\n' then
    if scan.previousCR then { scan with previousCR := false }
    else { scan.bump with previousCR := false }
  else if code == 0x000B || code == 0x000C || code == 0x0085 || code == 0x2028 ||
      code == 0x2029 then
    { scan.bump with previousCR := false }
  else
    { scan with previousCR := false }

/-- Scan logical breaks in a valid source interval without copying that interval. -/
private def logicalBreaksBetween (text : String) (start stop : text.Pos)
    (ordered : start ≤ stop) (initial : NewlineScan) : NewlineScan :=
  (text.slice start stop ordered).chars.fold NewlineScan.step initial

@[inline] private def NewlinePolicy.fires (policy : NewlinePolicy) (count : Nat) : Bool :=
  match policy with
  | .never => false
  | .always => 0 < count
  | .two => 2 ≤ count

@[inline] private def isSentenceFinal (character : Char) : Bool :=
  match character with
  | '.' | '!' | '?' => true
  | _ =>
      match character.toNat with
      | 0x0589  -- Armenian full stop
      | 0x061F  -- Arabic question mark
      | 0x06D4  -- Arabic full stop
      | 0x0964  -- Devanagari danda
      | 0x0965  -- Devanagari double danda
      | 0x1362  -- Ethiopic full stop
      | 0x1803  -- Mongolian full stop
      | 0x1809  -- Manchu full stop
      | 0x2026  -- horizontal ellipsis
      | 0x203C  -- double exclamation mark
      | 0x2047  -- double question mark
      | 0x2048  -- question exclamation mark
      | 0x2049  -- exclamation question mark
      | 0x2E2E  -- reversed question mark
      | 0x3002  -- ideographic full stop
      | 0xFE52  -- small full stop
      | 0xFE56  -- small question mark
      | 0xFE57  -- small exclamation mark
      | 0xFF01  -- fullwidth exclamation mark
      | 0xFF0E  -- fullwidth full stop
      | 0xFF1F  -- fullwidth question mark
      | 0xFF61  -- halfwidth ideographic full stop
        => true
      | _ => false

@[inline] private def isBoundaryFollower (character : Char) : Bool :=
  match character with
  | '\'' | '"' | ')' | ']' | '}' => true
  | _ =>
      match character.toNat with
      | 0x00BB  -- right-pointing double angle quotation mark
      | 0x2019  -- right single quotation mark
      | 0x201D  -- right double quotation mark
      | 0x203A  -- right-pointing single angle quotation mark
      | 0x3009  -- right angle bracket
      | 0x300B  -- right double angle bracket
      | 0x300D  -- right corner bracket
      | 0x300F  -- right white corner bracket
      | 0x3011  -- right black lenticular bracket
      | 0x3015  -- right tortoise shell bracket
      | 0x3017  -- right white lenticular bracket
      | 0x3019  -- right white tortoise shell bracket
      | 0x301B  -- right white square bracket
      | 0xFF09  -- fullwidth right parenthesis
      | 0xFF3D  -- fullwidth right square bracket
      | 0xFF5D  -- fullwidth right curly bracket
        => true
      | _ => false

/-- Test every scalar in a nonempty token without materializing its spelling. -/
@[inline] private def tokenAll (token : Token text) (predicate : Char → Bool) : Bool :=
  (text.slice token.startPos token.endPos (Nat.le_of_lt token.nonempty)).chars.all predicate

/-- Recognize a sentence-final scalar followed only by closing punctuation inside one token. -/
private def tokenHasTerminalSuffix (token : Token text) : Bool :=
  (text.slice token.startPos token.endPos (Nat.le_of_lt token.nonempty)).chars.fold
    (fun pending character ↦
      if isSentenceFinal character then true else pending && isBoundaryFollower character)
    false

/-- Detect an emitted line-feed token without copying its spelling. -/
@[inline] private def tokenStartsWithLineFeed (token : Token text) : Bool :=
  have notAtEnd : token.startPos ≠ text.endPos :=
    String.Pos.ne_of_lt <|
      String.Pos.lt_of_lt_of_le token.nonempty (String.Pos.le_endPos token.endPos)
  token.startPos.get notAtEnd == '\n'

private structure InitialismScan where
  valid : Bool := true
  segmentLength : Nat := 0
  periods : Nat := 0

@[inline] private def InitialismScan.step (scan : InitialismScan)
    (character : Char) : InitialismScan :=
  if !scan.valid then
    scan
  else if character.isAlpha then
    { scan with segmentLength := scan.segmentLength + 1 }
  else if character == '.' && 0 < scan.segmentLength && scan.segmentLength ≤ 3 then
    { scan with segmentLength := 0, periods := scan.periods + 1 }
  else
    { scan with valid := false }

/-- Protect compact dotted initialisms such as `U.S.` and `Ph.D.` from ordinary final periods. -/
private def tokenIsDottedInitialism (token : Token text) : Bool :=
  let scan :=
    (text.slice token.startPos token.endPos (Nat.le_of_lt token.nonempty)).chars.fold
      InitialismScan.step {}
  scan.valid && scan.segmentLength == 0 && 2 ≤ scan.periods

@[inline] private def tokenProvidesFinal (token : Token text) : Bool :=
  if tokenHasTerminalSuffix token then !tokenIsDottedInitialism token else false

private structure SplitState (text : String) where
  ends : Array Nat := #[]
  lastEnd : Nat := 0
  hasContent : Bool := false
  pendingFinal : Bool := false
  newlines : NewlineScan := {}
  previousEnd : Option text.Pos := none

/-- Close a nonempty range once; closing also consumes pending boundary evidence. -/
@[inline] private def SplitState.close (state : SplitState text)
    (endExclusive : Nat) : SplitState text :=
  if state.lastEnd < endExclusive then
    { state with
      ends := state.ends.push endExclusive
      lastEnd := endExclusive
      hasContent := false
      pendingFinal := false
      newlines := {} }
  else
    { state with pendingFinal := false, newlines := {} }

/-- Finish coverage without creating a trailing sentence made only of emitted newline tokens. -/
private def SplitState.finish (state : SplitState text) (size : Nat) : SplitState text :=
  if state.lastEnd < size then
    if state.hasContent || state.ends.isEmpty then
      state.close size
    else
      { state with ends := state.ends.pop.push size, lastEnd := size }
  else
    state

/-- Produce candidate boundaries during the single token-array traversal. -/
private def candidateEnds (config : Config) (source : Tokenization) : Array Nat :=
  if source.size = 0 then
    #[]
  else
    match config.mode with
    | .oneSentence => #[source.size]
    | mode => Id.run do
        let mut state : SplitState source.text := {}
        let newlinePolicy :=
          match mode with
          | .eolOnly => NewlinePolicy.always
          | _ => config.newlinePolicy
        for index in [0:source.tokens.size] do
          if inBounds : index < source.tokens.size then
            let token := source.tokens[index]

            -- Newlines in an ordered source gap precede all token-local rule evidence.
            let gapStart := state.previousEnd.getD source.text.startPos
            let adjacent := gapStart == token.startPos
            let gapNewlines :=
              if ordered : gapStart ≤ token.startPos then
                logicalBreaksBetween source.text gapStart token.startPos ordered state.newlines
              else
                {}
            state := { state with newlines := gapNewlines }
            let continuesCrLf :=
              adjacent && state.newlines.previousCR && token.kind == .newline &&
                tokenStartsWithLineFeed token
            if state.hasContent && newlinePolicy.fires state.newlines.count && !continuesCrLf then
              state := state.close index

            -- A punctuation run and all immediately trailing followers remain in one sentence.
            match mode with
            | .rules =>
                let final := tokenProvidesFinal token
                let follower := tokenAll token isBoundaryFollower
                let newline := token.kind == .newline
                if state.pendingFinal &&
                    (!adjacent || (!newline && !(final || follower))) then
                  state := state.close index
                state := { state with
                  pendingFinal :=
                    if newline then state.pendingFinal
                    else final || (state.pendingFinal && follower) }
            | .eolOnly =>
                state := { state with pendingFinal := false }
            | .oneSentence =>
                state := { state with pendingFinal := false }

            -- Emitted newline tokens carry their source break and attach to the range they close.
            match token.kind with
            | .newline =>
                let tokenNewlines := logicalBreaksBetween source.text token.startPos token.endPos
                  (Nat.le_of_lt token.nonempty) state.newlines
                state := { state with newlines := tokenNewlines }
                if state.hasContent &&
                    (state.pendingFinal || newlinePolicy.fires state.newlines.count) &&
                    !state.newlines.previousCR then
                  state := state.close (index + 1)
            | _ =>
                state := { state with newlines := {}, hasContent := true }

            state := { state with previousEnd := some token.endPos }

        return (state.finish source.size).ends

/-!
Candidate normalization is independent of linguistic rules.  Besides hardening the public API
against future rule changes, it makes the well-formedness proof depend only on a short structural
recursion over sentence ends, never on the scanner or Unicode tables.
-/

private def finishEndsFrom (size last : Nat) (lastLt : last < size) : List Nat → List Nat
  | [] => [size]
  | candidate :: candidates =>
      if accept : last < candidate ∧ candidate < size then
        candidate :: finishEndsFrom size candidate accept.2 candidates
      else
        finishEndsFrom size last lastLt candidates

private theorem mem_finishEndsFrom (size last : Nat) (lastLt : last < size)
    (candidates : List Nat) (value : Nat)
    (member : value ∈ finishEndsFrom size last lastLt candidates) :
    last < value ∧ value ≤ size := by
  induction candidates generalizing last with
  | nil =>
      simp only [finishEndsFrom, List.mem_singleton] at member
      subst value
      exact ⟨lastLt, Nat.le_refl size⟩
  | cons candidate candidates induction =>
      rw [finishEndsFrom] at member
      split at member
      · rename_i accept
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ⟨accept.1, Nat.le_of_lt accept.2⟩
        · have bounds := induction candidate accept.2 member
          exact ⟨Nat.lt_trans accept.1 bounds.1, bounds.2⟩
      · exact induction last lastLt member

private theorem pairwise_finishEndsFrom (size last : Nat) (lastLt : last < size)
    (candidates : List Nat) :
    (finishEndsFrom size last lastLt candidates).Pairwise (fun left right => left < right) := by
  induction candidates generalizing last with
  | nil => simp [finishEndsFrom]
  | cons candidate candidates induction =>
      rw [finishEndsFrom]
      split
      · rename_i accept
        exact List.pairwise_cons.mpr ⟨
          fun value member =>
            (mem_finishEndsFrom size candidate accept.2 candidates value member).1,
          induction candidate accept.2⟩
      · exact induction last lastLt

private theorem getLast?_finishEndsFrom (size last : Nat) (lastLt : last < size)
    (candidates : List Nat) :
    (finishEndsFrom size last lastLt candidates).getLast? = some size := by
  induction candidates generalizing last with
  | nil => simp [finishEndsFrom]
  | cons candidate candidates induction =>
      rw [finishEndsFrom]
      split
      · rename_i accept
        apply List.getLast?_eq_some_iff.mpr
        obtain ⟨initial, initialEq⟩ := List.getLast?_eq_some_iff.mp
          (induction candidate accept.2)
        exact ⟨candidate :: initial, by simp [initialEq]⟩
      · exact induction last lastLt

/-- Runtime accumulator for direct array normalization. -/
private structure NormalizeState where
  lastAccepted : Nat := 0
  ends : Array Nat := #[]

@[inline] private def NormalizeState.step (size : Nat) (state : NormalizeState)
    (candidate : Nat) : NormalizeState :=
  if _accept : state.lastAccepted < candidate ∧ candidate < size then
    { lastAccepted := candidate, ends := state.ends.push candidate }
  else
    state

private theorem normalizeFold_spec (size last : Nat) (lastLt : last < size)
    (accepted : Array Nat) (candidates : List Nat) :
    let result := candidates.foldl (NormalizeState.step size)
      { lastAccepted := last, ends := accepted }
    result.ends.toList ++ [size] =
      accepted.toList ++ finishEndsFrom size last lastLt candidates := by
  induction candidates generalizing last accepted with
  | nil => simp [finishEndsFrom]
  | cons candidate candidates induction =>
      rw [finishEndsFrom]
      split
      · rename_i accept
        simpa [NormalizeState.step, accept, List.append_assoc] using
          induction candidate accept.2 (accepted.push candidate)
      · rename_i rejected
        simpa [NormalizeState.step, rejected] using induction last lastLt accepted

/-- Retain increasing in-range candidates and install the unique mandatory final boundary. -/
private def normalizeEnds (size : Nat) (candidates : Array Nat) : Array Nat :=
  if _empty : size = 0 then
    #[]
  else
    let initial : NormalizeState := {
      ends := Array.emptyWithCapacity candidates.size
    }
    let state := candidates.foldl (NormalizeState.step size) initial
    state.ends.push size

private theorem normalizeEnds_eq_spec (size : Nat) (candidates : Array Nat)
    (nonempty : 0 < size) :
    (normalizeEnds size candidates).toList =
      finishEndsFrom size 0 nonempty candidates.toList := by
  have sizeNe := Nat.ne_of_gt nonempty
  have spec := normalizeFold_spec size 0 nonempty
    (Array.emptyWithCapacity candidates.size) candidates.toList
  simpa [normalizeEnds, sizeNe] using spec

private theorem pairwise_normalizeEnds (size : Nat) (candidates : Array Nat) :
    (normalizeEnds size candidates).toList.Pairwise (fun left right => left < right) := by
  by_cases empty : size = 0
  · simp [normalizeEnds, empty]
  · have nonempty := Nat.zero_lt_of_ne_zero empty
    rw [normalizeEnds_eq_spec size candidates nonempty]
    exact pairwise_finishEndsFrom size 0 nonempty candidates.toList

private theorem mem_normalizeEnds (size : Nat) (candidates : Array Nat) (value : Nat)
    (member : value ∈ (normalizeEnds size candidates).toList) :
    0 < value ∧ value ≤ size := by
  by_cases empty : size = 0
  · simp [normalizeEnds, empty] at member
  · have nonempty := Nat.zero_lt_of_ne_zero empty
    rw [normalizeEnds_eq_spec size candidates nonempty] at member
    exact mem_finishEndsFrom size 0 nonempty candidates.toList value member

private theorem normalizeEnds_nil_iff (size : Nat) (candidates : Array Nat) :
    (normalizeEnds size candidates).toList = [] ↔ size = 0 := by
  by_cases empty : size = 0
  · simp [normalizeEnds, empty]
  · have nonempty := Nat.zero_lt_of_ne_zero empty
    constructor
    · intro normalizedEmpty
      rw [normalizeEnds_eq_spec size candidates nonempty] at normalizedEmpty
      have final := getLast?_finishEndsFrom size 0 nonempty candidates.toList
      exfalso
      simp [normalizedEmpty] at final
    · exact fun contradiction => (empty contradiction).elim

private theorem getLast?_normalizeEnds (size : Nat) (candidates : Array Nat)
    (nonempty : 0 < size) :
    (normalizeEnds size candidates).toList.getLast? = some size := by
  rw [normalizeEnds_eq_spec size candidates nonempty]
  exact getLast?_finishEndsFrom size 0 nonempty candidates.toList

/-- Split a tokenization according to the selected deterministic policy. -/
def split (source : Tokenization) (config : Config := {}) : Segmentation :=
  { source, ends := normalizeEnds source.size (candidateEnds config source) }

/-- Every result of `split` has canonical, total token-index boundaries. -/
theorem split_wf (source : Tokenization) (config : Config := {}) :
    (split source config).WF := by
  refine ⟨pairwise_normalizeEnds source.size (candidateEnds config source), ?_, ?_, ?_⟩
  · intro endExclusive member
    exact mem_normalizeEnds source.size (candidateEnds config source) endExclusive member
  · exact normalizeEnds_nil_iff source.size (candidateEnds config source)
  · exact getLast?_normalizeEnds source.size (candidateEnds config source)

end Nlp.Tokenize.Sentence
