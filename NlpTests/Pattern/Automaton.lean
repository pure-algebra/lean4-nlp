import Nlp.Pattern.Automaton

/-!
# Bounded Thompson automaton tests

Deterministic regressions cover compilation budgets, source ordinals, normalized matching,
overlap ordering, and nullable-search rejection. An exhaustive executable differential test checks
the compiled NFA against the independently shaped reference semantics over small regular
languages, binary inputs, and every nearby caller range.
-/

namespace NlpTests.Pattern.Automaton

open Nlp.Pattern

/-- Evaluate a natural-number atom against one absolute array position. -/
private def holds (input : Array Nat) (atom position : Nat) : Bool :=
  input[position]? == some atom

/-- Project proof-carrying matches to their stable public data. -/
private def triples (found : Array Match) : Array (Nat × Nat × Nat) :=
  found.map fun matched ↦ (matched.rule, matched.start, matched.stop)

/-- Run a Boolean query against a compiled machine, returning false on unexpected failure. -/
private def query (patterns : Array (Regular Nat))
    (run : Automaton Nat → Bool) : Bool :=
  match Automaton.compile patterns with
  | .ok automaton => run automaton
  | .error _ => false

/-- Empty compilation retains only the shared start state. -/
example : query #[] fun automaton ↦
    automaton.ruleCount == 0 && automaton.stateCount == 1 && automaton.edgeCount == 0 := by
  native_decide

/-- Exact acceptance includes nullable rules and preserves source-array ordinals. -/
example : query #[.epsilon, .atom 1, .star (.atom 2)] fun automaton ↦
    automaton.matchingRulesRange (holds #[1]) 1 0 0 == #[0, 2] &&
    automaton.matchingRulesRange (holds #[1]) 1 0 1 == #[1] := by
  native_decide

/-- Matching normalizes clipped and inverted ranges without slicing the input. -/
example : query #[.epsilon, .seq (.atom 1) (.atom 2)] fun automaton ↦
    automaton.matchingRulesRange (holds #[0, 1, 2]) 3 1 99 == #[1] &&
    automaton.matchingRulesRange (holds #[0, 1, 2]) 3 9 2 == #[0] := by
  native_decide

/-- Duplicate rules remain distinct deterministic source ordinals. -/
example : query #[.atom 1, .atom 1, .atom 2] fun automaton ↦
    automaton.matchingRulesRange (holds #[1]) 1 0 1 == #[0, 1] := by
  native_decide

/-- Source patterns used to check overlap ordering and nonoverlapping selection. -/
private def searchPatterns : Array (Regular Nat) :=
  #[.atom 1, .seq (.atom 1) (.atom 2), .seq (.atom 1) (.atom 2)]

/-- Overlapping results are ordered by start, stop, then source ordinal. -/
example : query searchPatterns fun automaton ↦
    triples (automaton.findOverlappingRange (holds #[1, 2, 1, 2]) 4 0 4) ==
      #[(0, 0, 1), (1, 0, 2), (2, 0, 2),
        (0, 2, 3), (1, 2, 4), (2, 2, 4)] := by
  native_decide

/-- Work and match budgets accept their exact bounds and fail at the next smaller value. -/
private def overlapBudgetChecks : Bool :=
  match Automaton.compile searchPatterns with
  | .error _ => false
  | .ok automaton =>
      let required := automaton.overlapWorkUpperBound 4 0 4
      let exact := automaton.findOverlappingRangeWith
        { maxWork := required, maxMatches := 6 } (holds #[1, 2, 1, 2]) 4 0 4
      let lowWork := automaton.findOverlappingRangeWith
        { maxWork := required - 1, maxMatches := 6 } (holds #[1, 2, 1, 2]) 4 0 4
      let lowMatches := automaton.findOverlappingRangeWith
        { maxWork := required, maxMatches := 5 } (holds #[1, 2, 1, 2]) 4 0 4
      let exactOk := match exact with
        | .ok found => triples found ==
            #[(0, 0, 1), (1, 0, 2), (2, 0, 2),
              (0, 2, 3), (1, 2, 4), (2, 2, 4)]
        | .error _ => false
      let workOk := match lowWork with
        | .error (.workBudget found limit) => found == required && limit + 1 == required
        | _ => false
      let matchesOk := match lowMatches with
        | .error (.matchBudget 6 5) => true
        | _ => false
      required == 425 && exactOk && workOk && matchesOk

example : overlapBudgetChecks = true := by native_decide

/-- Empty normalized searches allow zero matches at their exact scratch-work bound. -/
private def emptyOverlapBudget : Bool :=
  match Automaton.compile searchPatterns with
  | .error _ => false
  | .ok automaton =>
      let required := automaton.overlapWorkUpperBound 4 9 2
      required == automaton.stateCount &&
        match automaton.findOverlappingRangeWith
            { maxWork := required, maxMatches := 0 } (holds #[1, 2, 1, 2]) 4 9 2 with
        | .ok found => found.isEmpty
        | .error _ => false

example : emptyOverlapBudget = true := by native_decide

/-- Leftmost-longest search breaks exact-span ties by lower source ordinal. -/
example : query searchPatterns fun automaton ↦
    match automaton.findNonOverlappingRange (holds #[1, 2, 1, 2]) 4 0 4 with
    | .ok found => triples found == #[(1, 0, 2), (1, 2, 4)]
    | .error _ => false := by
  native_decide

/-- Nonoverlapping search skips unmatched positions while retaining full coordinates. -/
example : query #[.seq (.atom 1) (.atom 2)] fun automaton ↦
    match automaton.findNonOverlappingRange (holds #[0, 1, 2, 0, 1, 2]) 6 0 6 with
    | .ok found => triples found == #[(0, 1, 3), (0, 4, 6)]
    | .error _ => false := by
  native_decide

/-- Any nullable source rule is reported before iterative search begins. -/
example : query #[.atom 1, .star (.atom 2), .epsilon] fun automaton ↦
    automaton.nullableRuleOrdinals == #[1, 2] &&
    match automaton.findNonOverlappingRange (holds #[1]) 1 0 1 with
    | .error (.nullableRules rules) => rules == #[1, 2]
    | _ => false := by
  native_decide

/-- The public proof projection certifies positive match progress. -/
example (matched : Match) : 0 < matched.width :=
  matched.width_pos

/-- Rule, state, and edge limits fail at the first required resource count. -/
private def budgetChecks : Bool :=
  let rule := Automaton.compileWith { maxRules := 0 } #[.atom 1]
  let shared := Automaton.compileWith { maxStates := 0 } (#[] : Array (Regular Nat))
  let states := Automaton.compileWith { maxStates := 2 } #[.atom 1]
  let edges := Automaton.compileWith { maxEdges := 0 } #[.atom 1]
  let ruleOk := match rule with
    | .error (.ruleBudget 1 0) => true
    | _ => false
  let sharedOk := match shared with
    | .error (.stateBudget 1 0) => true
    | _ => false
  let statesOk := match states with
    | .error (.stateBudget 3 2) => true
    | _ => false
  let edgesOk := match edges with
    | .error (.edgeBudget 1 0) => true
    | _ => false
  ruleOk && sharedOk && statesOk && edgesOk

example : budgetChecks = true := by native_decide

/-- Small but compositionally varied regular languages for differential checking. -/
private def smallPatterns : Array (Regular Nat) :=
  let base : Array (Regular Nat) := #[.empty, .epsilon, .atom 0, .atom 1]
  Id.run do
    let mut output := base
    for body in base do
      output := output.push (.star body)
    for left in base do
      for right in base do
        output := output.push (.alt left right)
        output := output.push (.seq left right)
    output := output.push (.seq (.star (.atom 0)) (.atom 1))
    output := output.push (.star (.alt .epsilon (.atom 1)))
    return output

/-- Every binary input through length three. -/
private def binaryInputs : Array (Array Nat) :=
  #[#[], #[0], #[1], #[0, 0], #[0, 1], #[1, 0], #[1, 1],
    #[0, 0, 0], #[0, 0, 1], #[0, 1, 0], #[0, 1, 1],
    #[1, 0, 0], #[1, 0, 1], #[1, 1, 0], #[1, 1, 1]]

/-- Reference accepting ordinals for one source array and normalized range. -/
private def referenceRules (patterns : Array (Regular Nat)) (input : Array Nat)
    (start stop : Nat) : Array Nat := Id.run do
  let mut output := #[]
  for rule in [0:patterns.size] do
    match patterns[rule]? with
    | some pattern =>
        if pattern.matchesRange (holds input) input.size start stop then
          output := output.push rule
    | none => pure ()
  return output

/-- Reference nonempty overlaps in compiled result order using `Regular.endpoints`. -/
private def referenceOverlaps (patterns : Array (Regular Nat)) (input : Array Nat)
    (start stop : Nat) : Array (Nat × Nat × Nat) := Id.run do
  let range := normalizeRange input.size start stop
  let mut output := #[]
  for candidateStart in [range.start:range.stop] do
    for candidateStop in [candidateStart + 1:range.stop + 1] do
      for rule in [0:patterns.size] do
        match patterns[rule]? with
        | some pattern =>
            let endpoints := pattern.endpoints (holds input) candidateStart range.stop
            if endpoints.contains candidateStop then
              output := output.push (rule, candidateStart, candidateStop)
        | none => pure ()
  return output

/--
Exhaustively compare the compiled NFA with the reference semantics.

The grid includes empty, clipped, and inverted ranges for every binary input through length three.
-/
private def exhaustiveDifferential : Bool :=
  match Automaton.compile smallPatterns with
  | .error _ => false
  | .ok automaton => Id.run do
      for input in binaryInputs do
        for start in [0:input.size + 3] do
          for stop in [0:input.size + 3] do
            let expected := referenceRules smallPatterns input start stop
            let actual := automaton.matchingRulesRange (holds input) input.size start stop
            if actual != expected then
              return false
      return true

example : exhaustiveDifferential = true := by native_decide

/-- Exhaustively compare bounded and unbounded overlap content with the reference semantics. -/
private def exhaustiveOverlapDifferential : Bool :=
  match Automaton.compile smallPatterns with
  | .error _ => false
  | .ok automaton => Id.run do
      for input in binaryInputs do
        for start in [0:input.size + 3] do
          for stop in [0:input.size + 3] do
            let expected := referenceOverlaps smallPatterns input start stop
            let actual := triples <| automaton.findOverlappingRange
              (holds input) input.size start stop
            let required := automaton.overlapWorkUpperBound input.size start stop
            let bounded := automaton.findOverlappingRangeWith
              { maxWork := required, maxMatches := expected.size }
              (holds input) input.size start stop
            if actual != expected then
              return false
            match bounded with
            | .ok found =>
                if triples found != expected then
                  return false
            | .error _ => return false
      return true

example : exhaustiveOverlapDifferential = true := by native_decide

/-- Nonnullable patterns used by the executable nonoverlapping reference policy. -/
private def nonnullablePatterns : Array (Regular Nat) :=
  #[.atom 0, .atom 1, .seq (.atom 0) (.atom 1),
    .seq (.atom 0) (.atom 1), .alt (.atom 0) (.atom 1)]

/-- Reference longest match at one start, breaking equal stops by lower source ordinal. -/
private def referenceBestAt? (patterns : Array (Regular Nat)) (input : Array Nat)
    (start stop : Nat) : Option (Nat × Nat × Nat) := Id.run do
  let mut bestRule : Option Nat := none
  let mut bestStop := start
  for candidateStop in [start + 1:stop + 1] do
    for rule in [0:patterns.size] do
      match patterns[rule]? with
      | some pattern =>
          let endpoints := pattern.endpoints (holds input) start stop
          if endpoints.contains candidateStop then
            match bestRule with
            | none =>
                bestRule := some rule
                bestStop := candidateStop
            | some incumbent =>
                if bestStop < candidateStop ||
                    (bestStop == candidateStop && rule < incumbent) then
                  bestRule := some rule
                  bestStop := candidateStop
      | none => pure ()
  return bestRule.map fun rule ↦ (rule, start, bestStop)

/-- Reference progress-safe leftmost-longest selection over one normalized range. -/
private def referenceNonOverlapping (patterns : Array (Regular Nat)) (input : Array Nat)
    (start stop : Nat) : Array (Nat × Nat × Nat) := Id.run do
  let range := normalizeRange input.size start stop
  let mut output := #[]
  let mut cursor := range.start
  for _ in [0:range.width] do
    if cursor < range.stop then
      match referenceBestAt? patterns input cursor range.stop with
      | none => cursor := cursor + 1
      | some matched =>
          output := output.push matched
          cursor := matched.2.2
  return output

/-- Exhaustively compare nonoverlapping policy with an independent reference implementation. -/
private def exhaustiveNonOverlappingDifferential : Bool :=
  match Automaton.compile nonnullablePatterns with
  | .error _ => false
  | .ok automaton => Id.run do
      for input in binaryInputs do
        for start in [0:input.size + 3] do
          for stop in [0:input.size + 3] do
            let expected := referenceNonOverlapping nonnullablePatterns input start stop
            match automaton.findNonOverlappingRange (holds input) input.size start stop with
            | .ok found =>
                if triples found != expected then
                  return false
            | .error _ => return false
      return true

example : exhaustiveNonOverlappingDifferential = true := by native_decide

/-- Check public search invariants without using the private match constructor. -/
private def validSearchOutput (size lower upper : Nat) (found : Array Match) : Bool := Id.run do
  let mut previous : Option Match := none
  for matched in found do
    let inBounds := lower ≤ matched.start && matched.start < matched.stop &&
      matched.stop ≤ min upper size
    if !inBounds then
      return false
    match previous with
    | none => pure ()
    | some prior =>
        let ordered := prior.start < matched.start ||
          (prior.start == matched.start &&
            (prior.stop < matched.stop ||
              (prior.stop == matched.stop && prior.rule ≤ matched.rule)))
        if !ordered then
          return false
    previous := some matched
  return true

/-- Exhaustive overlap output obeys range, width, and deterministic ordering invariants. -/
private def exhaustiveOverlapInvariants : Bool :=
  match Automaton.compile smallPatterns with
  | .error _ => false
  | .ok automaton => Id.run do
      for input in binaryInputs do
        let found := automaton.findOverlappingRange (holds input) input.size 0 99
        if !validSearchOutput input.size 0 99 found then
          return false
      return true

example : exhaustiveOverlapInvariants = true := by native_decide

end NlpTests.Pattern.Automaton
