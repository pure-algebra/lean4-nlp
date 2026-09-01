import Nlp.Pattern.Regular

/-!
# Bounded Thompson automata

Regular token patterns compile to an immutable Thompson NFA with compact state identifiers and
compressed outgoing-edge tables. Matching evaluates atoms symbolically against absolute input
positions. Compilation preserves source-array ordinals, enforces explicit allocation budgets, and
hides the automaton constructor so callers cannot manufacture invalid transition tables.
-/

namespace Nlp.Pattern

/-- Resource policy for compiling a collection of regular token rules. -/
structure CompileConfig where
  /-- Maximum number of NFA states, including the shared start state. -/
  maxStates : Nat := 65_536
  /-- Maximum combined number of epsilon and atom transitions. -/
  maxEdges : Nat := 262_144
  /-- Maximum number of source rules. -/
  maxRules : Nat := 65_536
  deriving Repr, DecidableEq, Inhabited

/-- Resource policy for bounded overlapping search over one normalized input range. -/
structure SearchConfig where
  /-- Maximum conservative work bound accepted before matching begins. -/
  maxWork : Nat := 67_108_864
  /-- Maximum number of proof-carrying matches retained in the result. -/
  maxMatches : Nat := 1_048_576
  deriving Repr, DecidableEq, Inhabited

/-- Why a bounded regular-pattern automaton could not be compiled. -/
inductive CompileError where
  /-- The source array exceeded the configured rule budget. -/
  | ruleBudget (required limit : Nat)
  /-- Rule ordinals exhausted their compact representation. -/
  | ruleCapacity (count : Nat)
  /-- Thompson construction exceeded the configured state budget. -/
  | stateBudget (required limit : Nat)
  /-- State identifiers exhausted their compact representation. -/
  | stateCapacity (count : Nat)
  /-- Thompson construction exceeded the configured combined edge budget. -/
  | edgeBudget (required limit : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One private epsilon edge during Thompson construction. -/
private structure EpsilonEdge where
  source : UInt32
  target : UInt32

/-- One private symbolic consuming edge during Thompson construction. -/
private structure AtomEdge (Atom : Type u) where
  source : UInt32
  atom : Atom
  target : UInt32

/-- Entry and exit states for one Thompson fragment. -/
private structure Fragment where
  start : UInt32
  stop : UInt32

/-- Mutable-by-value state used only while compiling a bounded NFA. -/
private structure Builder (Atom : Type u) where
  nextState : Nat := 0
  epsilonEdges : Array EpsilonEdge := #[]
  atomEdges : Array (AtomEdge Atom) := #[]

/-- Allocate one checked compact state identifier. -/
private def Builder.fresh (config : CompileConfig) (builder : Builder Atom) :
    Except CompileError (Builder Atom × UInt32) :=
  if config.maxStates ≤ builder.nextState then
    .error (.stateBudget (builder.nextState + 1) config.maxStates)
  else if !(builder.nextState < UInt32.size) then
    .error (.stateCapacity builder.nextState)
  else
    .ok ({ builder with nextState := builder.nextState + 1 }, UInt32.ofNat builder.nextState)

/-- Append one epsilon transition under the shared edge budget. -/
private def Builder.addEpsilon (config : CompileConfig) (builder : Builder Atom)
    (source target : UInt32) : Except CompileError (Builder Atom) :=
  let used := builder.epsilonEdges.size + builder.atomEdges.size
  if config.maxEdges ≤ used then
    .error (.edgeBudget (used + 1) config.maxEdges)
  else
    .ok { builder with epsilonEdges := builder.epsilonEdges.push ⟨source, target⟩ }

/-- Append one symbolic consuming transition under the shared edge budget. -/
private def Builder.addAtom (config : CompileConfig) (builder : Builder Atom)
    (source : UInt32) (atom : Atom) (target : UInt32) :
    Except CompileError (Builder Atom) :=
  let used := builder.epsilonEdges.size + builder.atomEdges.size
  if config.maxEdges ≤ used then
    .error (.edgeBudget (used + 1) config.maxEdges)
  else
    .ok { builder with atomEdges := builder.atomEdges.push ⟨source, atom, target⟩ }

/-- Compile one typed pattern to a bounded Thompson fragment. -/
private def compileRegular (config : CompileConfig) (builder : Builder Atom) :
    Regular Atom → Except CompileError (Builder Atom × Fragment)
  | .empty => do
      let (builder, start) ← builder.fresh config
      let (builder, stop) ← builder.fresh config
      return (builder, ⟨start, stop⟩)
  | .epsilon => do
      let (builder, start) ← builder.fresh config
      let (builder, stop) ← builder.fresh config
      let builder ← builder.addEpsilon config start stop
      return (builder, ⟨start, stop⟩)
  | .atom value => do
      let (builder, start) ← builder.fresh config
      let (builder, stop) ← builder.fresh config
      let builder ← builder.addAtom config start value stop
      return (builder, ⟨start, stop⟩)
  | .alt left right => do
      let (builder, start) ← builder.fresh config
      let (builder, stop) ← builder.fresh config
      let (builder, leftFragment) ← compileRegular config builder left
      let (builder, rightFragment) ← compileRegular config builder right
      let builder ← builder.addEpsilon config start leftFragment.start
      let builder ← builder.addEpsilon config start rightFragment.start
      let builder ← builder.addEpsilon config leftFragment.stop stop
      let builder ← builder.addEpsilon config rightFragment.stop stop
      return (builder, ⟨start, stop⟩)
  | .seq left right => do
      let (builder, leftFragment) ← compileRegular config builder left
      let (builder, rightFragment) ← compileRegular config builder right
      let builder ← builder.addEpsilon config leftFragment.stop rightFragment.start
      return (builder, ⟨leftFragment.start, rightFragment.stop⟩)
  | .star body => do
      let (builder, start) ← builder.fresh config
      let (builder, stop) ← builder.fresh config
      let (builder, fragment) ← compileRegular config builder body
      let builder ← builder.addEpsilon config start stop
      let builder ← builder.addEpsilon config start fragment.start
      let builder ← builder.addEpsilon config fragment.stop stop
      let builder ← builder.addEpsilon config fragment.stop fragment.start
      return (builder, ⟨start, stop⟩)

/-- Build compressed epsilon-edge offsets and targets in deterministic insertion order. -/
private def buildEpsilonCsr (stateCount : Nat) (edges : Array EpsilonEdge) :
    Array Nat × Array UInt32 := Id.run do
  let mut buckets : Array (Array UInt32) := Array.replicate stateCount #[]
  for edge in edges do
    let source := edge.source.toNat
    buckets := buckets.set! source ((buckets.getD source #[]).push edge.target)
  let mut offsets := Array.emptyWithCapacity (stateCount + 1)
  let mut targets := Array.emptyWithCapacity edges.size
  for bucket in buckets do
    offsets := offsets.push targets.size
    for target in bucket do
      targets := targets.push target
  offsets := offsets.push targets.size
  return (offsets, targets)

/-- Build parallel compressed symbolic-edge tables in deterministic insertion order. -/
private def buildAtomCsr (stateCount : Nat) (edges : Array (AtomEdge Atom)) :
    Array Nat × Array UInt32 × Array Atom := Id.run do
  let mut buckets : Array (Array (Atom × UInt32)) := Array.replicate stateCount #[]
  for edge in edges do
    let source := edge.source.toNat
    buckets := buckets.set! source ((buckets.getD source #[]).push (edge.atom, edge.target))
  let mut offsets := Array.emptyWithCapacity (stateCount + 1)
  let mut targets := Array.emptyWithCapacity edges.size
  let mut atoms := Array.emptyWithCapacity edges.size
  for bucket in buckets do
    offsets := offsets.push targets.size
    for (atom, target) in bucket do
      atoms := atoms.push atom
      targets := targets.push target
  offsets := offsets.push targets.size
  return (offsets, targets, atoms)

/-- A constructor-protected bounded Thompson NFA for ordered source rules. -/
structure Automaton (Atom : Type u) where
  private mk ::
  /-- Number of valid compact state identifiers. -/
  stateCount : Nat
  /-- Shared epsilon fan-out state for every source rule. -/
  private startState : UInt32
  /-- Compressed epsilon-edge offsets, with one terminal sentinel. -/
  private epsilonOffsets : Array Nat
  /-- Compressed epsilon-edge targets. -/
  private epsilonTargets : Array UInt32
  /-- Compressed symbolic-edge offsets, with one terminal sentinel. -/
  private atomOffsets : Array Nat
  /-- Compressed symbolic-edge targets. -/
  private atomTargets : Array UInt32
  /-- Symbolic predicates parallel to `atomTargets`. -/
  private atoms : Array Atom
  /-- One accepting state per source rule, in source order. -/
  private acceptStates : Array UInt32
  /-- Source ordinals whose languages accept an empty range. -/
  private nullableRules : Array Nat

namespace Automaton

/-- Number of source rules retained by the compiled automaton. -/
@[inline] def ruleCount (automaton : Automaton Atom) : Nat :=
  automaton.acceptStates.size

/-- Number of epsilon and consuming transitions retained by the compiled automaton. -/
@[inline] def edgeCount (automaton : Automaton Atom) : Nat :=
  automaton.epsilonTargets.size + automaton.atomTargets.size

/-- Source ordinals whose compiled patterns accept empty ranges. -/
@[inline] def nullableRuleOrdinals (automaton : Automaton Atom) : Array Nat :=
  automaton.nullableRules

/-- Compile ordered regular rules under an explicit resource policy. -/
def compileWith (config : CompileConfig) (patterns : Array (Regular Atom)) :
    Except CompileError (Automaton Atom) := do
  if config.maxRules < patterns.size then
    throw <| .ruleBudget patterns.size config.maxRules
  if UInt32.size < patterns.size then
    throw <| .ruleCapacity patterns.size
  let (builder, startState) ← ({} : Builder Atom).fresh config
  let mut builder := builder
  let mut acceptStates := Array.emptyWithCapacity patterns.size
  let mut nullableRules := #[]
  for pattern in patterns do
    let rule := acceptStates.size
    let (nextBuilder, fragment) ← compileRegular config builder pattern
    let nextBuilder ← nextBuilder.addEpsilon config startState fragment.start
    builder := nextBuilder
    acceptStates := acceptStates.push fragment.stop
    if pattern.nullable then
      nullableRules := nullableRules.push rule
  let (epsilonOffsets, epsilonTargets) :=
    buildEpsilonCsr builder.nextState builder.epsilonEdges
  let (atomOffsets, atomTargets, atoms) := buildAtomCsr builder.nextState builder.atomEdges
  return .mk builder.nextState startState epsilonOffsets epsilonTargets atomOffsets atomTargets
    atoms acceptStates nullableRules

/-- Compile ordered regular rules with the default resource policy. -/
@[inline] def compile (patterns : Array (Regular Atom)) : Except CompileError (Automaton Atom) :=
  compileWith {} patterns

/-- A duplicate-free active-state set identified by one scratch generation. -/
private structure StateSet where
  generation : Nat
  items : Array UInt32

/-- Reusable generation-stamped membership storage for all state sets in one public call. -/
private structure Scratch where
  generation : Nat
  marks : Array Nat

/-- Allocate the one state-sized scratch array used by a top-level matching call. -/
@[inline] private def Scratch.empty (stateCount : Nat) : Scratch :=
  ⟨0, Array.replicate stateCount 0⟩

/-- Clear a state set in constant time by advancing the unbounded generation stamp. -/
@[inline] private def Scratch.fresh (scratch : Scratch) : Scratch × StateSet :=
  let generation := scratch.generation + 1
  ({ scratch with generation := generation }, ⟨generation, #[]⟩)

/-- Insert one in-bounds compact state once in the set's generation. -/
@[inline] private def StateSet.insert (states : StateSet) (scratch : Scratch)
    (state : UInt32) : Scratch × StateSet :=
  let index := state.toNat
  if index < scratch.marks.size && scratch.marks.getD index 0 != states.generation then
    ({ scratch with marks := scratch.marks.set! index states.generation },
      { states with items := states.items.push state })
  else
    (scratch, states)

/-- Test generation-stamped membership without exposing the scratch representation. -/
@[inline] private def StateSet.contains (states : StateSet) (scratch : Scratch)
    (state : UInt32) : Bool :=
  scratch.marks.getD state.toNat 0 == states.generation

/-- Saturate seed states under bounded epsilon reachability. -/
private def epsilonClosure (automaton : Automaton Atom) (initialScratch : Scratch)
    (seeds : StateSet) : Scratch × StateSet := Id.run do
  let mut scratch := initialScratch
  let mut output := seeds
  for cursor in [0:automaton.stateCount] do
    match output.items[cursor]? with
    | none => return (scratch, output)
    | some state =>
      let source := state.toNat
      let first := automaton.epsilonOffsets.getD source 0
      let after := automaton.epsilonOffsets.getD (source + 1) first
      for edge in [first:after] do
        match automaton.epsilonTargets[edge]? with
        | none => pure ()
        | some target =>
            let inserted := output.insert scratch target
            scratch := inserted.1
            output := inserted.2
  return (scratch, output)

/-- Epsilon-closed shared start state. -/
private def startSet (automaton : Automaton Atom) (initialScratch : Scratch) :
    Scratch × StateSet :=
  let (scratch, empty) := initialScratch.fresh
  let (scratch, seeds) := empty.insert scratch automaton.startState
  epsilonClosure automaton scratch seeds

/-- Consume one symbolic input position and epsilon-close the resulting state set. -/
private def advance (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (position : Nat) (initialScratch : Scratch) (active : StateSet) :
    Scratch × StateSet := Id.run do
  let (nextScratch, empty) := initialScratch.fresh
  let mut scratch := nextScratch
  let mut seeds := empty
  for state in active.items do
    let source := state.toNat
    let first := automaton.atomOffsets.getD source 0
    let after := automaton.atomOffsets.getD (source + 1) first
    for edge in [first:after] do
      match automaton.atoms[edge]?, automaton.atomTargets[edge]? with
      | some atom, some target =>
          if holdsAt atom position then
            let inserted := seeds.insert scratch target
            scratch := inserted.1
            seeds := inserted.2
      | _, _ => pure ()
  return epsilonClosure automaton scratch seeds

/-- Return accepting source ordinals in deterministic source-array order. -/
private def acceptingRules (automaton : Automaton Atom) (scratch : Scratch)
    (active : StateSet) : Array Nat := Id.run do
  let mut output := #[]
  for rule in [0:automaton.acceptStates.size] do
    match automaton.acceptStates[rule]? with
    | some state =>
        if active.contains scratch state then
          output := output.push rule
    | none => pure ()
  return output

/--
Return every source rule accepting one normalized symbolic-input range.

The evaluator receives the full-column absolute position. No token array or range slice is owned
by the automaton.
-/
def matchingRulesRange (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (size start stop : Nat) : Array Nat := Id.run do
  let range := normalizeRange size start stop
  let started := startSet automaton (Scratch.empty automaton.stateCount)
  let mut scratch := started.1
  let mut active := started.2
  for position in [range.start:range.stop] do
    let stepped := advance automaton holdsAt position scratch active
    scratch := stepped.1
    active := stepped.2
    if active.items.isEmpty then
      return #[]
  return acceptingRules automaton scratch active

/-- Decide whether one source rule accepts a normalized symbolic-input range. -/
@[inline] def acceptsRange (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (size start stop rule : Nat) : Bool :=
  (automaton.matchingRulesRange holdsAt size start stop).contains rule

/--
Conservative work bound for overlapping search over one normalized range.

The bound charges one state-sized scratch initialization, one state-and-epsilon closure per start,
and one complete state, edge, and accepting-rule scan per possible consumed position. Early dead
state sets only reduce actual work.
-/
def overlapWorkUpperBound (automaton : Automaton Atom) (size start stop : Nat) : Nat :=
  let width := (normalizeRange size start stop).width
  let positions := width * (width + 1) / 2
  let startClosure := automaton.stateCount + automaton.epsilonTargets.size
  let step := 2 * automaton.stateCount + automaton.edgeCount + automaton.ruleCount
  automaton.stateCount + width * startClosure + positions * step

end Automaton

/-- One proof-carrying, nonempty regular-pattern match. -/
structure Match where
  private mk ::
  /-- Source-rule ordinal in compilation order. -/
  rule : Nat
  /-- Inclusive absolute symbolic-input position. -/
  start : Nat
  /-- Exclusive absolute symbolic-input position. -/
  stop : Nat
  /-- Search output never contains a zero-width match. -/
  private nonempty : start < stop
  deriving Repr, DecidableEq

namespace Match

/-- Every emitted regular-pattern match consumes at least one input position. -/
theorem start_lt_stop (matched : Match) : matched.start < matched.stop :=
  matched.nonempty

/-- Number of symbolic input positions consumed by a match. -/
@[inline] def width (matched : Match) : Nat :=
  matched.stop - matched.start

/-- Every emitted match has strictly positive width. -/
theorem width_pos (matched : Match) : 0 < matched.width :=
  Nat.sub_pos_iff_lt.mpr matched.nonempty

end Match

/-- Why bounded overlapping or progress-safe nonoverlapping search could not run. -/
inductive SearchError where
  /-- Nullable rules make a zero-width iterative search policy ambiguous. -/
  | nullableRules (rules : Array Nat)
  /-- Conservative overlapping-search work exceeded the caller's limit. -/
  | workBudget (required limit : Nat)
  /-- Overlapping search attempted to retain more matches than the caller allowed. -/
  | matchBudget (required limit : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Automaton

/-- Enumerate every nonempty match beginning at one fixed absolute position. -/
private def matchesAt (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (initialScratch : Scratch) (start stop : Nat) : Scratch × Array Match := Id.run do
  let mut output := #[]
  let started := startSet automaton initialScratch
  let mut scratch := started.1
  let mut active := started.2
  for position in [start:stop] do
    let stepped := advance automaton holdsAt position scratch active
    scratch := stepped.1
    active := stepped.2
    if active.items.isEmpty then
      return (scratch, output)
    if valid : start < position + 1 then
      for rule in acceptingRules automaton scratch active do
        output := output.push (.mk rule start (position + 1) valid)
  return (scratch, output)

/-- Stream one anchored candidate set directly into the shared overlapping result array. -/
private def appendMatchesAt (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (maxMatches : Option Nat) (initialScratch : Scratch) (initial : Array Match)
    (start stop : Nat) : Except SearchError (Scratch × Array Match) := do
  let mut output := initial
  let started := startSet automaton initialScratch
  let mut scratch := started.1
  let mut active := started.2
  for position in [start:stop] do
    let stepped := advance automaton holdsAt position scratch active
    scratch := stepped.1
    active := stepped.2
    if active.items.isEmpty then
      return (scratch, output)
    if valid : start < position + 1 then
      for rule in [0:automaton.acceptStates.size] do
        match automaton.acceptStates[rule]? with
        | some state =>
            if active.contains scratch state then
              match maxMatches with
              | some limit =>
                  if limit ≤ output.size then
                    throw <| .matchBudget (output.size + 1) limit
                  output := output.push (.mk rule start (position + 1) valid)
              | none => output := output.push (.mk rule start (position + 1) valid)
        | none => pure ()
  return (scratch, output)

/-- Collect overlapping matches without staging a temporary array for each start position. -/
private def findOverlappingCore (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (maxMatches : Option Nat) (size start stop : Nat) : Except SearchError (Array Match) := do
  let range := normalizeRange size start stop
  let mut scratch := Scratch.empty automaton.stateCount
  let mut output := #[]
  for candidateStart in [range.start:range.stop] do
    let found ←
      appendMatchesAt automaton holdsAt maxMatches scratch output candidateStart range.stop
    scratch := found.1
    output := found.2
  return output

/--
Find every nonempty match under explicit work and output budgets.

The conservative work bound is checked before scratch allocation or atom evaluation. Match output
is checked immediately before every emission. Successful results are ordered by start, then stop,
then source-rule ordinal.
-/
def findOverlappingRangeWith (automaton : Automaton Atom) (config : SearchConfig)
    (holdsAt : Atom → Nat → Bool) (size start stop : Nat) :
    Except SearchError (Array Match) :=
  let required := automaton.overlapWorkUpperBound size start stop
  if config.maxWork < required then
    .error (.workBudget required config.maxWork)
  else
    findOverlappingCore automaton holdsAt (some config.maxMatches) size start stop

/--
Find every nonempty match in a normalized symbolic-input range.

Results are ordered by start, then stop, then source-rule ordinal. Empty matches are intentionally
not emitted; use `matchingRulesRange` when exact empty-range acceptance is needed. This
compatibility wrapper has no work or output budget; prefer `findOverlappingRangeWith` at untrusted
boundaries.
-/
def findOverlappingRange (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (size start stop : Nat) : Array Match :=
  match findOverlappingCore automaton holdsAt none size start stop with
  | .ok found => found
  | .error _ => #[]

/-- Prefer a longer match, breaking exact span ties by lower source ordinal. -/
@[inline] private def preferred (candidate incumbent : Match) : Bool :=
  incumbent.stop < candidate.stop ||
    (candidate.stop == incumbent.stop && candidate.rule < incumbent.rule)

/-- Select the leftmost-starting rule's longest match with deterministic ordinal ties. -/
private def bestAt? (candidates : Array Match) : Option Match := Id.run do
  let mut best := none
  for candidate in candidates do
    match best with
    | none => best := some candidate
    | some incumbent =>
        if preferred candidate incumbent then
          best := some candidate
  return best

/--
Find a progress-safe leftmost-longest sequence of nonoverlapping matches.

The operation rejects a compiled rule set containing any nullable pattern. At each unmatched
position it advances by one; after a match it advances to that match's proven-larger stop. Exact
span ties retain the lowest source-rule ordinal.
-/
def findNonOverlappingRange (automaton : Automaton Atom) (holdsAt : Atom → Nat → Bool)
    (size start stop : Nat) : Except SearchError (Array Match) :=
  if automaton.nullableRules.isEmpty then
    .ok <| Id.run do
      let range := normalizeRange size start stop
      let mut scratch := Scratch.empty automaton.stateCount
      let mut output := #[]
      let mut cursor := range.start
      for _ in [0:range.width] do
        if cursor < range.stop then
          let found := matchesAt automaton holdsAt scratch cursor range.stop
          scratch := found.1
          match bestAt? found.2 with
          | none => cursor := cursor + 1
          | some matched =>
              output := output.push matched
              cursor := matched.stop
      return output
  else
    .error (.nullableRules automaton.nullableRules)

end Automaton

end Nlp.Pattern
