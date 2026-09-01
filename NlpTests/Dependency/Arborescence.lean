import Nlp.Dependency.Arborescence

/-!
# Nonprojective arborescence regression tests

The test oracle enumerates parent functions directly, validates them with the public dependency-
tree checker, and sums exact binary64 dyadic values. Reported operational `Float` costs are checked
separately in dependent order. The oracle shares no contraction logic with the optimized decoder.
-/

namespace NlpTests.Dependency.Arborescence

open Nlp Nlp.Dependency

/-- One finite single-root tree found by the independent exhaustive oracle. -/
private structure OracleResult where
  heads : Array Nat
  exactCost : Nat

/-- Decode one base-`n` parent-function code while skipping each dependent's self head. -/
private def headColumn (n code : Nat) : Array Nat :=
  Array.ofFn (n := n) fun index ↦
    let dependent := index.val + 1
    let digit := code / n ^ index.val % n
    if digit < dependent then digit else digit + 1

/-- Enumerate exactly the well-formed single-root parent functions over `n` real tokens. -/
private def validHeadColumns (n : Nat) : Array (Array Nat) := Id.run do
  if n = 0 then
    return #[]
  let mut output := Array.emptyWithCapacity (n ^ (n - 1))
  for code in [0:n ^ n] do
    let heads := headColumn n code
    if (checkSentenceTree heads).isOk then
      output := output.push heads
  return output

/-- Convert one nonnegative finite binary64 value to units of the least positive subnormal. -/
private def exactUnits? (value : Float) : Option Nat :=
  let raw := value.toBits.toNat
  let exponent := raw / 2 ^ 52 % 2 ^ 11
  let fraction := raw % 2 ^ 52
  if 2 ^ 63 ≤ raw then
    none
  else if exponent = 0 then
    some fraction
  else if exponent < 2 ^ 11 - 1 then
    some ((2 ^ 52 + fraction) * 2 ^ (exponent - 1))
  else
    none

/-- Interpret common least-subnormal units as one canonical exact public dyadic. -/
private def exactDyadic (units : Nat) : Dyadic :=
  Dyadic.ofIntWithPrec (Int.ofNat units) 1074

/-- Sum one candidate's exact binary64 dyadics without intermediate rounding. -/
private def exactOriginalCost? (arcs : ArcScores) (heads : Array Nat) : Option Nat := Id.run do
  unless heads.size = arcs.n do
    return none
  let mut total := 0
  for index in [0:heads.size] do
    match arcs.choice? heads[index]! (index + 1) with
    | none => return none
    | some choice =>
        let some units := exactUnits? choice.cost
          | return none
        total := total + units
  return some total

/-- Recompute one public result cost with the documented dependent-order `Float` fold. -/
private def operationalCost? (arcs : ArcScores) (heads : Array Nat) : Option Float := Id.run do
  unless heads.size = arcs.n do
    return none
  let mut total := 0.0
  for index in [0:heads.size] do
    match arcs.choice? heads[index]! (index + 1) with
    | none => return none
    | some choice => total := total + choice.cost
  if total.isFinite then some total else none

/-- Find a minimum finite single-root tree without sharing decoder internals. -/
private def oracle? (arcs : ArcScores) : Option OracleResult := Id.run do
  let mut best : Option OracleResult := none
  for heads in validHeadColumns arcs.n do
    match exactOriginalCost? arcs heads with
    | none => pure ()
    | some exactCost =>
      match best with
      | none => best := some ⟨heads, exactCost⟩
      | some current =>
        if exactCost < current.exactCost then
          best := some ⟨heads, exactCost⟩
  return best

/-- Stable ordinal of one legal root or real-token arc in dependency-major order. -/
private def legalArcOrdinal (n head dependent : Nat) : Nat :=
  if head = 0 then
    dependent - 1
  else
    let headOrdinal := if head < dependent then head - 1 else head - 2
    n + (dependent - 1) * (n - 1) + headOrdinal

/-- Decode one ternary fixture digit as exact zero, exact one, or a forbidden arc. -/
private def ternaryCost (code ordinal : Nat) : Float :=
  match code / 3 ^ ordinal % 3 with
  | 0 => 0.0
  | 1 => 1.0
  | _ => inf

/-- Compile one of all ternary three-token directed score graphs. -/
private def ternaryArcs? (code : Nat) : Option ArcScores :=
  (ArcScores.compileScorer 3 #["root", "dep"] 0 fun head dependent _ ↦
    ternaryCost code (legalArcOrdinal 3 head dependent)).toOption

/-- All three-token graphs over the exact cost alphabet `{0, 1, forbidden}`. -/
private def ternaryGraphCount : Nat :=
  3 ^ 9

/-- Check every public result field against its compiled original arc choices. -/
private def resultConsistent (arcs : ArcScores) (result : Arborescence.Result) : Bool := Id.run do
  unless result.heads.size = arcs.n && result.relations.size = arcs.n do
    return false
  unless (checkSentenceTree result.heads).isOk && result.heads.count 0 = 1 do
    return false
  for index in [0:arcs.n] do
    let some head := result.heads[index]?
      | return false
    let some relation := result.relations[index]?
      | return false
    let some choice := arcs.choice? head (index + 1)
      | return false
    unless relation = choice.relation do
      return false
  let some units := exactOriginalCost? arcs result.heads
    | return false
  unless result.exactCost = exactDyadic units do
    return false
  match operationalCost? arcs result.heads, result.reportedCost? with
  | none, none => return true
  | some expected, some reported => return expected.toBits = reported.toBits
  | _, _ => return false

/-- Exact bits of a present operational report. -/
private def reportedBits? (result : Arborescence.Result) : Option UInt64 :=
  result.reportedCost?.map Float.toBits

/-- Compare one optimized result with the independent finite minimum. -/
private def oracleParity (arcs : ArcScores) : Bool :=
  match oracle? arcs, Arborescence.parse? arcs with
  | none, .ok none => true
  | some expected, .ok (some result) =>
      match exactOriginalCost? arcs result.heads with
      | some exactCost => resultConsistent arcs result && exactCost = expected.exactCost
      | none => false
  | _, _ => false

/-- Exhaustively compare all ternary three-token graphs with the parent-function oracle. -/
private def exhaustiveTernaryParity : Bool := Id.run do
  for code in [0:ternaryGraphCount] do
    let some arcs := ternaryArcs? code
      | return false
    unless oracleParity arcs do
      return false
  return true

/-- Compile one fixture through the public checked arc-score boundary. -/
private def fixtureArcs? (n : Nat) (labels : Array String)
    (score : ArcScores.Scorer) : Option ArcScores :=
  (ArcScores.compileScorer n labels 0 score).toOption

/-- Unique crossing optimum with exact source-relation identities. -/
private def crossingArcs? : Option ArcScores :=
  fixtureArcs? 4 #["root", "dep", "obj"] fun head dependent relation ↦
    if head = 0 && dependent = 3 then
      0.0
    else if head = 3 && dependent = 1 && relation = 2 then
      0.0
    else if head = 4 && dependent = 2 && relation = 1 then
      0.0
    else if head = 3 && dependent = 4 && relation = 2 then
      0.0
    else
      inf

/-- A two-cycle whose equal raw root entries have unequal reduced costs. -/
private def twoCycleArcs? : Option ArcScores :=
  fixtureArcs? 2 #["root", "dep"] fun head dependent relation ↦
    if head = 0 then
      10.0
    else if relation = 1 && head = 2 && dependent = 1 then
      5.0
    else if relation = 1 && head = 1 && dependent = 2 then
      7.0
    else
      inf

/-- Root-heavy ties where the unconstrained optimum violates the one-root contract. -/
private def rootHeavyArcs? : Option ArcScores :=
  fixtureArcs? 3 #["root", "dep"] fun head _dependent relation ↦
    if head = 0 then 0.0 else if relation = 1 then 100.0 else inf

/-- Fully tied dense fixture for deterministic contraction and expansion. -/
private def tiedArcs? : Option ArcScores :=
  fixtureArcs? 4 #["root", "dep"] fun head _dependent relation ↦
    if head = 0 || relation = 1 then 0.0 else inf

/-- No finite directed arc exists. -/
private def forbiddenArcs? : Option ArcScores :=
  fixtureArcs? 3 #["root", "dep"] fun _head _dependent _relation ↦ inf

/-- Only the invalid multi-root star exists. -/
private def multiRootOnlyArcs? : Option ArcScores :=
  fixtureArcs? 3 #["root", "dep"] fun head _dependent _relation ↦
    if head = 0 then 0.0 else inf

/-- Empty checked arc table. -/
private def emptyArcs? : Option ArcScores :=
  fixtureArcs? 0 #["root"] fun _head _dependent _relation ↦ 0.0

/-- One exact root arc for the singleton regression. -/
private def singletonArcs? : Option ArcScores :=
  fixtureArcs? 1 #["root"] fun _head _dependent _relation ↦ 0.25

/-- Eight-token fixture that contracts `1↔2`, then the accumulated cycle with each next token. -/
private def nestedCycleArcs? : Option ArcScores :=
  fixtureArcs? 8 #["root", "dep"] fun head dependent relation ↦
    if head = 0 && dependent = 1 then
      1.0
    else if relation = 1 && dependent = 1 && 2 ≤ head then
      0.0
    else if relation = 1 && head = 1 && 2 ≤ dependent then
      0.0
    else
      inf

/-- Three disjoint selected two-cycles connected by unique external entering arcs. -/
private def disjointCycleArcs? : Option ArcScores :=
  fixtureArcs? 6 #["root", "dep"] fun head dependent relation ↦
    if head = 0 && dependent = 1 then
      3.0
    else if relation != 1 then
      inf
    else if (head = 1 && dependent = 2) || (head = 2 && dependent = 1) then
      0.0
    else if (head = 3 && dependent = 4) || (head = 4 && dependent = 3) then
      0.0
    else if (head = 5 && dependent = 6) || (head = 6 && dependent = 5) then
      0.0
    else if (head = 2 && dependent = 3) || (head = 4 && dependent = 5) then
      1.0
    else
      inf

/-- Explicitly asymmetric graph that detects head/dependent coordinate transposition. -/
private def asymmetricArcs? : Option ArcScores :=
  fixtureArcs? 2 #["root", "dep"] fun head dependent relation ↦
    if head = 0 && dependent = 2 then
      1.0
    else if head = 2 && dependent = 1 && relation = 1 then
      2.0
    else if head = 0 && dependent = 1 then
      10.0
    else if head = 1 && dependent = 2 && relation = 1 then
      20.0
    else
      inf

/-- A finite three-token component plus one dependent with no incoming edge. -/
private def disconnectedArcs? : Option ArcScores :=
  fixtureArcs? 4 #["root", "dep"] fun head dependent relation ↦
    if head = 0 && dependent = 1 then
      0.0
    else if relation = 1 && head + 1 = dependent && dependent ≤ 3 then
      0.0
    else
      inf

/-- Unique tree whose individually finite original costs overflow when accumulated. -/
private def overflowArcs? : Option ArcScores :=
  fixtureArcs? 2 #["root", "dep"] fun head dependent relation ↦
    if head = 0 && dependent = 1 then
      1.0e308
    else if relation = 1 && head = 1 && dependent = 2 then
      1.0e308
    else
      inf

/-- A unique two-token tree spanning the least subnormal through the largest finite binary64. -/
private def wideExponentArcs? : Option ArcScores :=
  fixtureArcs? 2 #["root", "dep"] fun head dependent relation ↦
    if head = 0 && dependent = 1 then
      Float.ofBits 1
    else if relation = 1 && head = 1 && dependent = 2 then
      Float.ofBits 0x7fefffffffffffff
    else
      inf

/-- Adjacent binary64 values whose exact tie has unequal dependent-order rounded totals. -/
private def adjacentFloatArcs? : Option ArcScores :=
  let costs : Array Float := #[
    inf,
    Float.ofBits 1,
    inf,
    inf,
    Float.ofBits 0x3ff0000000000001,
    Float.ofBits 1,
    1.0,
    0.5,
    inf,
    0.0,
    Float.ofBits 0x3ff0000000000001,
    inf,
    inf,
    1.0,
    Float.ofBits 0x3ff0000000000001,
    Float.ofBits 0x3ff0000000000001]
  fixtureArcs? 4 #["root", "dep"] fun head dependent relation ↦
    if head = 0 || relation = 1 then
      costs.getD (legalArcOrdinal 4 head dependent) inf
    else
      inf

/-- Rounded cycle reductions hide a strict two-subnormal-unit exact improvement. -/
private def strictExactArcs? : Option ArcScores :=
  fixtureArcs? 4 #["root", "dep"] fun head dependent relation ↦
    if head = 0 && dependent = 2 then
      Float.ofBits 2
    else if head = 0 && dependent = 3 then
      Float.ofBits 0x3fffffffffffffff
    else if relation = 1 && head = 2 && dependent = 1 then
      0.0
    else if relation = 1 && head = 3 && dependent = 2 then
      Float.ofBits 0x3fffffffffffffff
    else if relation = 1 && head = 2 && dependent = 3 then
      Float.ofBits 0x400fffffffffffff
    else if relation = 1 && head = 2 && dependent = 4 then
      0.0
    else
      inf

/-- The independent conversion covers zero, subnormal, normal, adjacent, and nonfinite values. -/
private def exactUnitConversion : Bool :=
  exactUnits? 0.0 == some 0 &&
    exactUnits? (Float.ofBits 1) == some 1 &&
    exactUnits? 0.5 == some (2 ^ 1073) &&
    exactUnits? 1.0 == some (2 ^ 1074) &&
    exactUnits? (Float.ofBits 0x3ff0000000000001) ==
      some (2 ^ 1074 + 2 ^ 1022) &&
    (exactUnits? inf).isNone

#guard exactUnitConversion

/-- Cayley's count checks independently validate the parent-function enumerator. -/
example :
    (validHeadColumns 1).size = 1 ∧
      (validHeadColumns 2).size = 2 ∧
      (validHeadColumns 3).size = 9 ∧
      (validHeadColumns 4).size = 64 ∧
      (validHeadColumns 5).size = 625 := by
  native_decide

/-- Every ternary three-token graph agrees with the independent finite optimum. -/
example : exhaustiveTernaryParity = true := by
  native_decide

/-- The optimized kernel retains a unique nonprojective optimum and exact relation ordinals. -/
private def crossingOptimum : Bool :=
  match crossingArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs, Arborescence.parseNamed? arcs with
    | .ok (some result), .ok (some named) =>
      resultConsistent arcs result && result.heads == #[3, 4, 0, 3] &&
        result.relations == #[2, 1, 0, 2] &&
        reportedBits? result == some (0.0 : Float).toBits &&
        named.heads == result.heads && named.relations == #["obj", "dep", "root", "obj"] &&
        match checkProjective result.heads with
        | .error (.crossing 1 3 2 4) => true
        | _ => false
    | _, _ => false

#guard crossingOptimum

/-- Contraction chooses by adjusted entering cost and expands through the correct cycle member. -/
private def twoCycleExpansion : Bool :=
  match twoCycleArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs with
    | .ok (some result) =>
      resultConsistent arcs result && result.heads == #[2, 0] &&
        result.relations == #[1, 0] && reportedBits? result == some (15.0 : Float).toBits
    | _ => false

#guard twoCycleExpansion

/-- Nested contractions expand to the unique star without losing an original dependent. -/
private def nestedCycleExpansion : Bool :=
  match nestedCycleArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs with
    | .ok (some result) =>
      resultConsistent arcs result &&
        result.heads == #[0, 1, 1, 1, 1, 1, 1, 1] &&
        result.relations == #[0, 1, 1, 1, 1, 1, 1, 1] &&
        reportedBits? result == some (1.0 : Float).toBits
    | _ => false

#guard nestedCycleExpansion

/-- Independent selected cycles all expand through their unique external entering edges. -/
private def disjointCycleExpansion : Bool :=
  match disjointCycleArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs with
    | .ok (some result) =>
      resultConsistent arcs result && result.heads == #[0, 1, 2, 3, 4, 5] &&
        result.relations == #[0, 1, 1, 1, 1, 1] &&
        reportedBits? result == some (5.0 : Float).toBits
    | _ => false

#guard disjointCycleExpansion

/-- Source and target coordinates remain directional throughout score lookup and output. -/
private def asymmetricCoordinates : Bool :=
  match asymmetricArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs with
    | .ok (some result) =>
      resultConsistent arcs result && result.heads == #[2, 0] &&
        reportedBits? result == some (3.0 : Float).toBits
    | _ => false

#guard asymmetricCoordinates

/-- Symbolic root count outranks the cheaper invalid multi-root arborescence. -/
private def rootObjective : Bool :=
  match rootHeavyArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs with
    | .ok (some result) =>
      oracleParity arcs && resultConsistent arcs result && result.heads.count 0 == 1 &&
        reportedBits? result == some (200.0 : Float).toBits
    | _ => false

#guard rootObjective

/-- Exact ties are stable across complete contraction and expansion runs. -/
private def deterministicTies : Bool :=
  match tiedArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs, Arborescence.parse? arcs with
    | .ok (some first), .ok (some second) =>
      oracleParity arcs && resultConsistent arcs first && resultConsistent arcs second &&
        first.heads == #[0, 1, 1, 1] && first.relations == #[0, 1, 1, 1] &&
        first.heads == second.heads && first.relations == second.relations &&
        reportedBits? first == reportedBits? second
    | _, _ => false

#guard deterministicTies

/-- Exact dyadic ties use kernel coordinates, while public costs retain operational Float folds. -/
private def adjacentFloatExactObjective : Bool :=
  match adjacentFloatArcs? with
  | none => false
  | some arcs =>
    let alternative := #[4, 0, 1, 2]
    let selected := #[2, 0, 1, 1]
    match oracle? arcs, Arborescence.parse? arcs,
        exactOriginalCost? arcs alternative, exactOriginalCost? arcs selected,
        operationalCost? arcs alternative, operationalCost? arcs selected with
    | some expected, .ok (some result), some alternativeExact, some selectedExact,
        some alternativeOperational, some selectedOperational =>
      oracleParity arcs && resultConsistent arcs result && result.heads == selected &&
        result.relations == #[1, 0, 1, 1] && alternativeExact == selectedExact &&
        selectedExact == expected.exactCost &&
        alternativeOperational.toBits == (0x4008000000000000 : UInt64) &&
        selectedOperational.toBits == (0x4008000000000001 : UInt64) &&
        reportedBits? result == some selectedOperational.toBits
    | _, _, _, _, _, _ => false

#guard adjacentFloatExactObjective

/-- Exact reductions recover the strict optimum hidden by two equal rounded Float differences. -/
private def strictExactObjective : Bool :=
  match strictExactArcs? with
  | none => false
  | some arcs =>
    let roundedHeads := #[2, 0, 2, 2]
    let exactHeads := #[2, 3, 0, 2]
    match Arborescence.parse? arcs, exactOriginalCost? arcs roundedHeads,
        exactOriginalCost? arcs exactHeads, operationalCost? arcs exactHeads with
    | .ok (some result), some roundedExact, some selectedExact, some reported =>
      oracleParity arcs && resultConsistent arcs result && result.heads == exactHeads &&
        result.relations == #[1, 1, 0, 1] && selectedExact + 2 == roundedExact &&
        result.exactCost == exactDyadic selectedExact &&
        reported.toBits == (0x400fffffffffffff : UInt64) &&
        reportedBits? result == some reported.toBits
    | _, _, _, _ => false

#guard strictExactObjective

/-- Missing arcs and an exclusively multi-root graph both mean no one-root analysis. -/
private def absentAnalyses : Bool :=
  match forbiddenArcs?, multiRootOnlyArcs? with
  | some forbidden, some multiRootOnly =>
    (Arborescence.parse? forbidden matches .ok none) &&
      (Arborescence.parse? multiRootOnly matches .ok none) &&
      (oracle? forbidden).isNone && (oracle? multiRootOnly).isNone
  | _, _ => false

#guard absentAnalyses

/-- One dependent without any finite incoming arc makes a spanning analysis impossible. -/
private def disconnectedAnalysis : Bool :=
  match disconnectedArcs? with
  | none => false
  | some arcs =>
    (Arborescence.parse? arcs matches .ok none) && (oracle? arcs).isNone

#guard disconnectedAnalysis

/-- Empty input has no tree; a singleton preserves its exact root label and cost. -/
private def degenerateInputs : Bool :=
  match emptyArcs?, singletonArcs? with
  | some empty, some singleton =>
    (Arborescence.parse? empty matches .ok none) &&
      match Arborescence.parse? singleton with
      | .ok (some result) =>
        resultConsistent singleton result && result.heads == #[0] &&
          result.relations == #[0] && reportedBits? result == some (0.25 : Float).toBits
      | _ => false
  | _, _ => false

#guard degenerateInputs

/-- Reporting overflow preserves the exact optimum while omitting only its operational Float. -/
private def aggregateOverflow : Bool :=
  match overflowArcs? with
  | none => false
  | some arcs =>
    match Arborescence.parse? arcs with
    | .ok (some result) =>
      (oracle? arcs).isSome && (operationalCost? arcs #[0, 1]).isNone &&
        resultConsistent arcs result && result.heads == #[0, 1] && result.reportedCost?.isNone
    | _ => false

#guard aggregateOverflow

/-- The advertised workspace count is both sufficient and the exact preflight boundary. -/
private def workspaceBoundary : Bool :=
  match tiedArcs? with
  | none => false
  | some arcs =>
    let required := Arborescence.workspaceEntryCount arcs.n
    let exact : Arborescence.KernelConfig := { maxWorkspaceEntries := required }
    let short : Arborescence.KernelConfig := { maxWorkspaceEntries := required - 1 }
    match Arborescence.parseWith? exact arcs, Arborescence.parseWith? short arcs with
    | .ok (some result), .error (.workspaceBudget found limit) =>
      resultConsistent arcs result && found == required && limit == required - 1
    | _, _ => false

#guard workspaceBoundary

/-- Wide exact integers use their graph-specific limb bound as the exact preflight boundary. -/
private def limbAwareWorkspaceBoundary : Bool :=
  match wideExponentArcs? with
  | none => false
  | some arcs =>
    let baseline := Arborescence.workspaceEntryCount arcs.n
    let required := Arborescence.workspaceEntryCountFor arcs
    let exact : Arborescence.KernelConfig := { maxWorkspaceEntries := required }
    let short : Arborescence.KernelConfig := { maxWorkspaceEntries := required - 1 }
    match Arborescence.parseWith? exact arcs, Arborescence.parseWith? short arcs with
    | .ok (some result), .error (.workspaceBudget found limit) =>
      baseline < required && resultConsistent arcs result && result.heads == #[0, 1] &&
        found == required && limit == required - 1
    | _, _ => false

#guard limbAwareWorkspaceBoundary

/-- Successful outputs expose all checked structural and reporting properties as proof fields. -/
example (result : Arborescence.Result) :
    result.relations.size = result.heads.size ∧
      SentenceTreeWF result.heads ∧
      result.heads.count 0 = 1 ∧
      (match result.reportedCost? with
        | none => True
        | some value => value.isFinite = true) :=
  ⟨result.aligned, result.wellFormed, result.singleRoot, result.reportedFinite⟩

end NlpTests.Dependency.Arborescence
