import Nlp.Core.Data.Interner

/-!
# Exact token-phrase automata

This module compiles exact token phrases into an Aho--Corasick automaton. Input strings are
interned once at compilation; inference performs one exact vocabulary lookup per token and keeps
all state transitions on packed integer keys. Failure links avoid restarting from each token, and
dictionary-suffix links enumerate suffix rules without copying output arrays into trie nodes.

Ranges are normalized against the original form column. Matching never allocates a sentence slice,
and every result retains full-column half-open coordinates and its source-rule ordinal.
-/

namespace Nlp.Pattern

/-- Resource policy for exact phrase compilation. -/
structure PhraseCompileConfig where
  /-- Maximum number of trie nodes, including the root. -/
  maxNodes : Nat := 1_048_576
  /-- Maximum number of ordered source rules and terminal output ordinals. -/
  maxRules : Nat := 65_536
  /-- Maximum cumulative number of tokens across all source phrases. -/
  maxSourceTokens : Nat := 1_048_576
  deriving Repr, DecidableEq, Inhabited

/-- Why exact phrases could not be compiled into a bounded automaton. -/
inductive PhraseCompileError where
  /-- The source array exceeded the configured rule budget. -/
  | ruleBudget (required limit : Nat)
  /-- Rule ordinals do not fit in the compact identifier representation. -/
  | ruleCapacity (count : Nat)
  /-- Cumulative source tokens exceeded the configured input budget. -/
  | sourceTokenBudget (required limit : Nat)
  /-- A source rule contains no tokens and would produce a zero-width match. -/
  | emptyPhrase (rule : Nat)
  /-- One phrase token is empty. -/
  | emptyToken (rule token : Nat)
  /-- The exact token vocabulary exhausted its compact identifier space. -/
  | wordCapacity (count : Nat)
  /-- The configured trie-node budget cannot represent the source phrases. -/
  | nodeBudget (required limit : Nat)
  /-- Trie nodes exhausted their compact identifier representation. -/
  | nodeCapacity (count : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Why bounded exact-phrase search could not retain its result. -/
inductive PhraseSearchError where
  /-- Search attempted to retain more matches than the caller allowed. -/
  | matchBudget (required limit : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One nonempty exact-phrase match in full-input half-open token coordinates. -/
structure PhraseMatch where
  private mk ::
  /-- Source-rule ordinal in compilation order. -/
  rule : Nat
  /-- Inclusive token offset in the full input column. -/
  start : Nat
  /-- Exclusive token offset in the full input column. -/
  stop : Nat
  /-- Exact phrases cannot produce an empty match. -/
  private nonempty : start < stop
  deriving Repr, DecidableEq

namespace PhraseMatch

/-- Every compiled exact-phrase match consumes at least one token. -/
theorem start_lt_stop (matched : PhraseMatch) : matched.start < matched.stop :=
  matched.nonempty

/-- Number of tokens consumed by an exact-phrase match. -/
@[inline] def width (matched : PhraseMatch) : Nat :=
  matched.stop - matched.start

/-- Match width is strictly positive. -/
theorem width_pos (matched : PhraseMatch) : 0 < matched.width := by
  exact Nat.sub_pos_iff_lt.mpr matched.nonempty

end PhraseMatch

/-- One trie node with compact failure and dictionary-suffix links. -/
private structure PhraseNode where
  fail : UInt32 := 0
  dictionarySuffix : Option UInt32 := none
  outputs : Array UInt32 := #[]
  children : Array (UInt32 × UInt32) := #[]

/-- A validated immutable exact-phrase automaton. -/
structure PhraseAutomaton where
  private mk ::
  /-- Exact, case-sensitive token vocabulary. -/
  private words : Interner
  /-- Packed `(node, word)` transitions. -/
  private transitions : Std.HashMap UInt64 UInt32
  /-- Rooted trie with complete failure and dictionary-suffix links. -/
  private nodes : Array PhraseNode
  /-- Positive source-rule lengths in compilation order. -/
  private lengths : Array Nat

namespace PhraseAutomaton

/-- The empty rooted automaton is a lawful default with no source rules. -/
instance : Inhabited PhraseAutomaton where
  default := .mk {} {} #[{}] #[]

/-- Pack a compact trie node and word into one collision-free transition key. -/
@[inline] private def transitionKey (node word : UInt32) : UInt64 :=
  (node.toUInt64 <<< 32) ||| word.toUInt64

/-- Number of source rules retained by an exact-phrase automaton. -/
@[inline] def ruleCount (automaton : PhraseAutomaton) : Nat :=
  automaton.lengths.size

/-- Number of trie nodes, including the root. -/
@[inline] def nodeCount (automaton : PhraseAutomaton) : Nat :=
  automaton.nodes.size

/-- Number of distinct exact token spellings retained by the automaton. -/
@[inline] def vocabularySize (automaton : PhraseAutomaton) : Nat :=
  automaton.words.size

/-- Positive token width of a source rule, when the ordinal is valid. -/
@[inline] def ruleLength? (automaton : PhraseAutomaton) (rule : Nat) : Option Nat :=
  automaton.lengths[rule]?

/-- Normalize a caller-selected half-open range against one full input column. -/
@[inline] def normalizeRange (size start stop : Nat) : Nat × Nat :=
  let upper := min stop size
  (min start upper, upper)

/-- Adapt the persistent interner's only failure to phrase compilation. -/
private def wordError : Interner.Error → PhraseCompileError
  | .capacityExceeded count => .wordCapacity count

/-- Intern one checked source token while preserving deterministic diagnostics. -/
private def internToken (words : Interner) (rule token : Nat) (form : String) :
    Except PhraseCompileError (Interner × UInt32) :=
  if form.isEmpty then
    .error (.emptyToken rule token)
  else
    match words.intern form with
    | .ok result => .ok result
    | .error cause => .error (wordError cause)

/-- Append one outgoing trie edge to its source node. -/
private def appendChild (nodes : Array PhraseNode) (source word target : UInt32) :
    Array PhraseNode :=
  let node := nodes.getD source.toNat {}
  nodes.set! source.toNat { node with children := node.children.push (word, target) }

/-- Select the nearest suffix node that emits at least one direct source rule. -/
private def dictionarySuffix (nodes : Array PhraseNode) (fallback : UInt32) : Option UInt32 :=
  let node := nodes.getD fallback.toNat {}
  if node.outputs.isEmpty then node.dictionarySuffix else some fallback

/-- Follow failure links until one transition accepts `word` or the root is reached. -/
private def failureTransition (nodes : Array PhraseNode)
    (transitions : Std.HashMap UInt64 UInt32) (initial word : UInt32) : UInt32 := Id.run do
  let mut state := initial
  for _ in [0:nodes.size] do
    match transitions.get? (transitionKey state word) with
    | some target => return target
    | none =>
      if state == 0 then
        return 0
      state := (nodes.getD state.toNat {}).fail
  return 0

/-- Populate breadth-first failure and dictionary-suffix links after trie construction. -/
private def buildFailureLinks (initial : Array PhraseNode)
    (transitions : Std.HashMap UInt64 UInt32) : Array PhraseNode := Id.run do
  let root := initial.getD 0 {}
  let mut nodes := initial
  let mut queue := Array.emptyWithCapacity (nodes.size - 1)
  for (_, child) in root.children do
    let childNode := nodes.getD child.toNat {}
    nodes := nodes.set! child.toNat { childNode with fail := 0, dictionarySuffix := none }
    queue := queue.push child
  let mut head := 0
  while head < queue.size do
    let source := queue[head]!
    head := head + 1
    let sourceNode := nodes.getD source.toNat {}
    for (word, child) in sourceNode.children do
      let fallback := failureTransition nodes transitions sourceNode.fail word
      let childNode := nodes.getD child.toNat {}
      nodes := nodes.set! child.toNat
        { childNode with
          fail := fallback
          dictionarySuffix := dictionarySuffix nodes fallback }
      queue := queue.push child
  return nodes

/--
Validate source structure and allocation-driving counts before constructing compiler tables.

Empty diagnostics retain their original rule and token ordinals. The cumulative token budget is
checked only after the complete structural scan, so malformed source locations are not masked by
an earlier running-total overflow.
-/
private def validateSource (config : PhraseCompileConfig)
    (phrases : Array (Array String)) : Except PhraseCompileError Nat := do
  if config.maxRules < phrases.size then
    throw <| .ruleBudget phrases.size config.maxRules
  if !(phrases.size ≤ UInt32.size) then
    throw <| .ruleCapacity phrases.size
  let mut sourceTokens := 0
  for rule in [0:phrases.size] do
    let phrase := phrases[rule]!
    if phrase.isEmpty then
      throw <| .emptyPhrase rule
    for token in [0:phrase.size] do
      if phrase[token]!.isEmpty then
        throw <| .emptyToken rule token
    sourceTokens := sourceTokens + phrase.size
  if config.maxSourceTokens < sourceTokens then
    throw <| .sourceTokenBudget sourceTokens config.maxSourceTokens
  return sourceTokens

/--
Compile exact nonempty token phrases into a bounded Aho--Corasick automaton.

Source array order is retained as the public rule ordinal. Duplicate phrases remain distinct
rules. Trie prefixes share nodes, while failure and dictionary links enumerate suffix outputs.
-/
def compile (phrases : Array (Array String)) (config : PhraseCompileConfig := {}) :
    Except PhraseCompileError PhraseAutomaton := do
  let _sourceTokens ← validateSource config phrases
  if config.maxNodes = 0 then
    throw <| .nodeBudget 1 config.maxNodes
  let mut words := Interner.empty
  let mut transitions : Std.HashMap UInt64 UInt32 :=
    Std.HashMap.emptyWithCapacity phrases.size
  let mut nodes : Array PhraseNode := #[{}]
  let mut lengths := Array.emptyWithCapacity phrases.size
  for rule in [0:phrases.size] do
    let phrase := phrases[rule]!
    let mut state : UInt32 := 0
    for token in [0:phrase.size] do
      let (nextWords, word) ← internToken words rule token phrase[token]!
      words := nextWords
      let key := transitionKey state word
      match transitions.get? key with
      | some target => state := target
      | none =>
        if config.maxNodes ≤ nodes.size then
          throw <| .nodeBudget (nodes.size + 1) config.maxNodes
        if !(nodes.size < UInt32.size) then
          throw <| .nodeCapacity nodes.size
        let target := UInt32.ofNat nodes.size
        nodes := nodes.push {}
        nodes := appendChild nodes state word target
        transitions := transitions.insert key target
        state := target
    let terminal := nodes.getD state.toNat {}
    nodes := nodes.set! state.toNat
      { terminal with outputs := terminal.outputs.push (UInt32.ofNat rule) }
    lengths := lengths.push phrase.size
  return .mk words transitions (buildFailureLinks nodes transitions) lengths

/-- Advance the automaton by one known vocabulary identifier. -/
@[inline] private def advance (automaton : PhraseAutomaton) (state word : UInt32) : UInt32 :=
  failureTransition automaton.nodes automaton.transitions state word

/-- Emit direct and suffix outputs for one reached trie node. -/
private def emitMatches (automaton : PhraseAutomaton) (maxMatches : Option Nat)
    (lower upper stop : Nat) (initialState : UInt32) (initial : Array PhraseMatch) :
    Except PhraseSearchError (Array PhraseMatch) := do
  let mut output := initial
  let mut state? : Option UInt32 := some initialState
  for _ in [0:automaton.nodes.size] do
    match state? with
    | none => return output
    | some state =>
      let node := automaton.nodes.getD state.toNat {}
      for compactRule in node.outputs do
        let rule := compactRule.toNat
        let length := automaton.lengths.getD rule 0
        let start := stop - length
        if valid : lower ≤ start ∧ start < stop ∧ stop ≤ upper then
          match maxMatches with
          | some limit =>
              if limit ≤ output.size then
                throw <| .matchBudget (output.size + 1) limit
              output := output.push (.mk rule start stop valid.2.1)
          | none => output := output.push (.mk rule start stop valid.2.1)
      state? := node.dictionarySuffix
  return output

/-- Search one normalized range with an optional exact output bound. -/
private def findAllRangeCore (automaton : PhraseAutomaton) (maxMatches : Option Nat)
    (forms : Array String) (start stop : Nat) :
    Except PhraseSearchError (Array PhraseMatch) := do
  let (lower, upper) := normalizeRange forms.size start stop
  let mut state : UInt32 := 0
  let mut output : Array PhraseMatch := #[]
  for position in [lower:upper] do
    match automaton.words.lookup? forms[position]! with
    | none => state := 0
    | some word => state := automaton.advance state word
    output ← automaton.emitMatches maxMatches lower upper (position + 1) state output
  return output

/-- Find every exact phrase while enforcing an exact retained-match bound. -/
def findAllRangeWithLimit (automaton : PhraseAutomaton) (maxMatches : Nat)
    (forms : Array String) (start stop : Nat) :
    Except PhraseSearchError (Array PhraseMatch) :=
  automaton.findAllRangeCore (some maxMatches) forms start stop

/--
Find every exact phrase in a normalized half-open range without allocating an input slice.

Results retain full-input coordinates. The state machine resets at the normalized lower bound, so
no match can cross a caller-selected sentence boundary.
-/
def findAllRange (automaton : PhraseAutomaton) (forms : Array String)
    (start stop : Nat) : Array PhraseMatch :=
  match automaton.findAllRangeCore none forms start stop with
  | .ok found => found
  | .error _ => #[]

/-- Find every exact phrase in a complete form column. -/
@[inline] def findAll (automaton : PhraseAutomaton) (forms : Array String) :
    Array PhraseMatch :=
  automaton.findAllRange forms 0 forms.size

end PhraseAutomaton

end Nlp.Pattern
