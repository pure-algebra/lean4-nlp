import Nlp.Dependency.EnglishEnhanced

/-!
# English enhanced-dependency regression tests

Golden fixtures cover every rule in the bounded word-node transformer. A deliberately slow
list-based oracle rediscovers children by scanning the whole sentence, then checks every valid
head array through four words against the indexed implementation.
-/

namespace NlpTests.Dependency.EnglishEnhanced

open Nlp.Dependency
open Nlp.Dependency.EnglishEnhanced

/-- Compare relation bases without using transformer internals. -/
@[inline] private def oracleRelationIs (relation expected : String) : Bool :=
  relation == expected || relation.startsWith (expected ++ ":")

/-- Rediscover one parent's children with an intentionally quadratic list scan. -/
private def oracleChildren (heads : Array Nat) (parent : Nat) : List Nat :=
  (List.range heads.size).filterMap fun index ↦
    if heads[index]! = parent then some (index + 1) else none

/-- Read one one-based relation in an oracle sentence. -/
@[inline] private def oracleRelationAt (relations : Array String) (dependent : Nat) : String :=
  relations[dependent - 1]!

/-- Select the leftmost child in either marker family by a fresh full scan. -/
private def oracleLeftmostMarker? (heads : Array Nat) (relations : Array String)
    (dependent : Nat) (first second : String) : Option Nat :=
  (oracleChildren heads dependent).find? fun child ↦
    let relation := oracleRelationAt relations child
    oracleRelationIs relation first ||
      (!second.isEmpty && oracleRelationIs relation second)

/-- Select the nearest preceding direct `cc`, or the leftmost direct `cc`. -/
private def oracleConjunctionMarker? (heads : Array Nat) (relations : Array String)
    (dependent : Nat) : Option Nat :=
  let markers := (oracleChildren heads dependent).filter fun child ↦
    oracleRelationIs (oracleRelationAt relations child) "cc"
  let preceding := markers.foldl (fun current child ↦
    if child < dependent then some child else current) none
  preceding.orElse fun _ ↦ markers.head?

/-- Lowercase one usable oracle marker value. -/
private def oracleNormalized? (values : Array String) (dependent : Nat) : Option String :=
  let value := values[dependent - 1]!.toLower
  if value.isEmpty || value == "_" ||
      value.any fun character ↦
        character.isWhitespace || character == ':' || character == '|' then
    none
  else
    some value

/-- Join marker parts without sharing the production helper. -/
@[inline] private def oracleAppend (acc part : String) : String :=
  if acc.isEmpty then part else acc ++ "_" ++ part

/-- Rebuild a marker MWE by scanning all words in surface order. -/
private def oracleMarkerName? (heads : Array Nat) (relations forms lemmas : Array String)
    (marker : Nat) : Option String := do
  let fixed := (oracleChildren heads marker).filter fun word ↦
    oracleRelationIs (oracleRelationAt relations word) "fixed"
  if fixed.isEmpty then
    oracleNormalized? lemmas marker
  else
    let members := (List.range heads.size).map (fun index ↦ index + 1) |>.filter fun word ↦
      word = marker ||
        (heads[word - 1]! = marker &&
          oracleRelationIs (oracleRelationAt relations word) "fixed")
    let parts ← members.mapM fun word ↦ oracleNormalized? forms word
    return parts.foldl oracleAppend ""

/-- Independently select and normalize one lexicalized relation. -/
private def oracleLexicalized? (config : Config) (heads : Array Nat)
    (relations forms lemmas : Array String) (dependent : Nat) : Option String := do
  let relation := oracleRelationAt relations dependent
  let marker ←
    if config.lexicalizeNominals &&
        (oracleRelationIs relation "nmod" || oracleRelationIs relation "obl") then
      oracleLeftmostMarker? heads relations dependent "case" ""
    else if config.lexicalizeClauses &&
        (oracleRelationIs relation "acl" || oracleRelationIs relation "advcl") then
      oracleLeftmostMarker? heads relations dependent "mark" "case"
    else if config.lexicalizeConjunctions && oracleRelationIs relation "conj" then
      oracleConjunctionMarker? heads relations dependent
    else
      none
  let name ← oracleMarkerName? heads relations forms lemmas marker
  return relation ++ ":" ++ name

/-- Relations excluded by the independently stated propagation policy. -/
@[inline] private def oraclePropagationExcluded (relation : String) : Bool :=
  oracleRelationIs relation "conj" || oracleRelationIs relation "cc" ||
    oracleRelationIs relation "case" || oracleRelationIs relation "mark" ||
    oracleRelationIs relation "punct"

/-- Independently decide whether one conjunct inherits its governor's incoming arc. -/
private def oraclePropagates (config : Config) (heads : Array Nat)
    (relations : Array String) (dependent : Nat) : Bool :=
  if !config.propagateIncomingConj ||
      !oracleRelationIs (oracleRelationAt relations dependent) "conj" then
    false
  else
    let governor := heads[dependent - 1]!
    governor != 0 &&
      !oraclePropagationExcluded (oracleRelationAt relations governor)

/-- Map the oracle's basic head coordinate to a public graph node. -/
@[inline] private def oracleHead (head : Nat) : NodeId :=
  if head = 0 then .root else .word head

/-- Strict canonical order for the independent insertion sort. -/
private def oracleArcLess (left right : Arc String) : Bool :=
  match left.head.compare right.head with
  | .lt => true
  | .gt => false
  | .eq => compare left.relation right.relation == .lt

/-- Insert one arc into a canonical list without using array merge sort. -/
private def oracleInsertArc (arc : Arc String) : List (Arc String) → List (Arc String)
  | [] => [arc]
  | first :: rest =>
      if oracleArcLess arc first then arc :: first :: rest
      else first :: oracleInsertArc arc rest

/-- Canonically order oracle arcs with a slow list insertion sort. -/
private def oracleSortArcs (arcs : List (Arc String)) : Array (Arc String) :=
  (arcs.foldl (fun sorted arc ↦ oracleInsertArc arc sorted) []).toArray

/-- Independent expected rows and exact rule-family counts. -/
private structure Oracle where
  rows : Array (Row String)
  counts : Counts

/-- Evaluate the bounded rule set without sharing its child index or row builder. -/
private def oracle (config : Config) (heads : Array Nat)
    (relations forms lemmas : Array String) : Oracle := Id.run do
  let labels := Array.ofFn (n := heads.size) fun index ↦
    oracleLexicalized? config heads relations forms lemmas (index.val + 1)
  let mut lexicalized : Nat := 0
  let mut propagated : Nat := 0
  let mut rows := Array.emptyWithCapacity heads.size
  for index in [0:heads.size] do
    let dependent := index + 1
    let basicHead := heads[index]!
    let basicRelation := relations[index]!
    let basic : Arc String := ⟨oracleHead basicHead, basicRelation, .basic⟩
    if (labels[index]!).isSome then
      lexicalized := lexicalized + 1
    let arcs :=
      match labels[index]! with
      | none => [basic]
      | some relation =>
          [basic, ⟨oracleHead basicHead, relation, .enhanced⟩]
    let propagates := oraclePropagates config heads relations dependent
    if propagates then
      propagated := propagated + 1
    let arcs :=
      if propagates then
        let governor := basicHead
        let propagatedHead := heads[governor - 1]!
        let originalRelation := oracleRelationAt relations governor
        let propagatedRelation := (labels[governor - 1]!).getD originalRelation
        arcs ++ [⟨oracleHead propagatedHead, propagatedRelation, .enhanced⟩]
      else
        arcs
    rows := rows.push ⟨.word dependent, oracleSortArcs arcs⟩
  return ⟨rows, ⟨heads.size, lexicalized, propagated⟩⟩

/-- Compare the optimized public result with the independent oracle. -/
private def agreesWithOracle (config : Config) (heads : Array Nat)
    (relations forms lemmas pos : Array String) : Bool :=
  match enhanceArraysWith? config heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      let expected := oracle config heads relations forms lemmas
      decide (result.graph.toRows = expected.rows) &&
        decide (result.counts = expected.counts)

/-- Check for one exact public arc in a result row. -/
private def hasArc (result : Result) (dependent : Nat) (head : NodeId)
    (relation : String) (origin : Origin) : Bool :=
  match result.graph.incoming? (.word dependent) with
  | none => false
  | some row => row.incoming.any fun arc ↦
      arc.head == head && arc.relation == relation && arc.origin == origin

/-- Allocate inert form and POS columns for a rule fixture. -/
private def fixtureColumns (size : Nat) : Array String × Array String :=
  (Array.replicate size "x", Array.replicate size "X")

/-- Multiword nominal markers are lowercased and joined in surface order. -/
private def nominalFixedGolden : Bool :=
  let heads := #[0, 1, 2, 3, 3]
  let relations := #["root", "nmod", "case", "fixed", "fixed"]
  let forms := #["Book", "Table", "In", "Front", "Of"]
  let lemmas := #["book", "table", "in", "front", "of"]
  let pos := Array.replicate heads.size "X"
  match enhanceArrays? heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      decide (result.counts = ⟨5, 1, 0⟩) && result.graph.edgeCount == 6 &&
        hasArc result 2 (.word 1) "nmod" .basic &&
        hasArc result 2 (.word 1) "nmod:in_front_of" .enhanced

#guard nominalFixedGolden

/-- Fixed marker MWEs use normalized surface forms instead of inflection-changing lemmas. -/
private def clauseFixedGolden : Bool :=
  let heads := #[0, 1, 2, 3, 3]
  let relations := #["root", "advcl", "mark", "fixed", "fixed"]
  let forms := #["Left", "Stayed", "As", "Opposed", "To"]
  let lemmas := #["leave", "stay", "as", "oppose", "to"]
  let pos := Array.replicate heads.size "X"
  match enhanceArrays? heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      decide (result.counts = ⟨5, 1, 0⟩) &&
        hasArc result 2 (.word 1) "advcl:as_opposed_to" .enhanced &&
        !hasArc result 2 (.word 1) "advcl:as_oppose_to" .enhanced

#guard clauseFixedGolden

/-- Conjunct propagation reuses its governor's computed enhanced label. -/
private def computedLabelPropagationGolden : Bool :=
  let heads := #[0, 1, 2, 2, 4]
  let relations := #["root", "obl", "case", "conj", "cc"]
  let lemmas := #["Met", "Home", "In", "Office", "And"]
  let (forms, pos) := fixtureColumns heads.size
  match enhanceArrays? heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      decide (result.counts = ⟨5, 2, 1⟩) && result.graph.edgeCount == 8 &&
        hasArc result 4 (.word 2) "conj" .basic &&
        hasArc result 4 (.word 2) "conj:and" .enhanced &&
        hasArc result 4 (.word 1) "obl:in" .enhanced

#guard computedLabelPropagationGolden

/-- A root incoming relation propagates to a conjunct as an enhanced root arc. -/
private def rootPropagationGolden : Bool :=
  let heads := #[2, 0, 4, 2]
  let relations := #["nsubj", "root", "cc", "conj"]
  let lemmas := #["They", "Run", "And", "Jump"]
  let (forms, pos) := fixtureColumns heads.size
  match enhanceArrays? heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      decide (result.counts = ⟨4, 1, 1⟩) &&
        hasArc result 4 .root "root" .enhanced &&
        hasArc result 4 (.word 2) "conj:and" .enhanced

#guard rootPropagationGolden

/-- The nearest preceding `cc` wins even when other direct markers surround a conjunct. -/
private def nearestConjunctionGolden : Bool :=
  let heads := #[0, 4, 4, 1, 4]
  let relations := #["root", "cc", "cc", "conj", "cc"]
  let lemmas := #["Go", "But", "And", "Stay", "Or"]
  let (forms, pos) := fixtureColumns heads.size
  match enhanceArrays? heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      hasArc result 4 (.word 1) "conj:and" .enhanced &&
        !hasArc result 4 (.word 1) "conj:but" .enhanced &&
        !hasArc result 4 (.word 1) "conj:or" .enhanced

#guard nearestConjunctionGolden

/-- With no preceding `cc`, coordination uses the leftmost direct marker. -/
private def leftmostConjunctionGolden : Bool :=
  let heads := #[0, 1, 2, 2]
  let relations := #["root", "conj", "cc", "cc"]
  let lemmas := #["Go", "Stay", "And", "Or"]
  let (forms, pos) := fixtureColumns heads.size
  match enhanceArrays? heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      hasArc result 2 (.word 1) "conj:and" .enhanced &&
        !hasArc result 2 (.word 1) "conj:or" .enhanced

#guard leftmostConjunctionGolden

/-- A flattened range reads full columns in place and emits sentence-local nodes. -/
private def rangeGolden : Bool :=
  let heads := #[0, 0, 1, 2, 3, 0]
  let relations := #["root", "root", "advcl", "mark", "fixed", "root"]
  let lemmas := #["Before", "Left", "Stayed", "Because", "Of", "After"]
  let forms := #["Before", "Left", "Stayed", "Because", "Of", "After"]
  let pos := Array.replicate heads.size "X"
  match enhanceRange? heads relations forms lemmas pos 1 5 with
  | .error _ => false
  | .ok result =>
      result.graph.nodeCount == 4 &&
        hasArc result 2 (.word 1) "advcl:because_of" .enhanced

#guard rangeGolden

/-- Empty aligned arrays compile to the unique empty graph. -/
private def emptyGolden : Bool :=
  match enhanceArrays? #[] #[] #[] #[] #[] with
  | .error _ => false
  | .ok result =>
      result.graph.nodeCount == 0 && result.graph.edgeCount == 0 &&
        decide (result.counts = ⟨0, 0, 0⟩)

#guard emptyGolden

/- Root heads require the exact `root` label. -/
#guard match enhanceArrays? #[0, 1] #["dep", "obj"] #["x", "x"]
    #["x", "x"] #["X", "X"] with
  | .error (.rootRelationMismatch 1 0 "dep") => true
  | _ => false

/- The `root` label cannot appear on a non-root basic edge. -/
#guard match enhanceArrays? #[0, 1] #["root", "root"] #["x", "x"]
    #["x", "x"] #["X", "X"] with
  | .error (.rootRelationMismatch 2 1 "root") => true
  | _ => false

/-- Checked trees still receive lexical-column and root-label validation. -/
private def checkedTreeBoundary : Bool :=
  match Tree.ofArrays #[0, 1] #["dep", "obj"] with
  | .error _ => false
  | .ok tree =>
      match enhanceTree? tree #["x", "x"] #["x", "x"] #["X", "X"] with
      | .error (.rootRelationMismatch 1 0 "dep") => true
      | _ => false

#guard checkedTreeBoundary

/-- The checked-tree wrapper produces the same canonical graph as raw aligned arrays. -/
private def checkedTreeParity : Bool :=
  let heads := #[0, 1, 2, 3]
  let relations := #["root", "advcl", "mark", "fixed"]
  let lemmas := #["Left", "Stayed", "Because", "Of"]
  let (forms, pos) := fixtureColumns heads.size
  match Tree.ofArrays heads relations with
  | .error _ => false
  | .ok tree =>
      match enhanceTree? tree forms lemmas pos,
          enhanceArrays? heads relations forms lemmas pos with
      | .ok checked, .ok raw =>
          decide (checked.graph.toRows = raw.graph.toRows) &&
            decide (checked.counts = raw.counts)
      | _, _ => false

#guard checkedTreeParity

/-- Alignment, range, and range-local tree failures retain exact public coordinates. -/
private def inputBoundaryErrors : Bool :=
  let relationCount :=
    match enhanceArrays? #[0] #[] #["x"] #["x"] #["X"] with
    | .error (.relationCount 1 0) => true
    | _ => false
  let reversedRange :=
    match enhanceRange? #[0] #["root"] #["x"] #["x"] #["X"] 1 0 with
    | .error (.invalidRange 1 0 1) => true
    | _ => false
  let localHead :=
    match enhanceRange? #[0, 0, 3] #["root", "root", "obj"]
        #["x", "x", "x"] #["x", "x", "x"] #["X", "X", "X"] 1 3 with
    | .error (.invalidTree (.headOutOfRange 2 3 2)) => true
    | _ => false
  relationCount && reversedRange && localHead

#guard inputBoundaryErrors

/-- One malformed relation fixture is rejected at its local dependent coordinate. -/
private def rejectsInvalidRelation (relation : String) : Bool :=
  match enhanceArrays? #[0, 1] #["root", relation] #["x", "x"]
      #["x", "x"] #["X", "X"] with
  | .error (.invalidRelation 2 found) => found == relation
  | _ => false

/-- Empty sections and CoNLL-U delimiters cannot cross the relation boundary. -/
private def invalidRelationBoundary : Bool :=
  ["", "_", ":obj", "obj:", "obj::agent", "bad label", "bad\tlabel",
    "bad\nlabel", "bad|label"].all rejectsInvalidRelation

#guard invalidRelationBoundary

/-- Unsafe marker lemmas skip lexicalization instead of creating malformed graph labels. -/
private def invalidMarkerGolden : Bool :=
  let heads := #[0, 1, 2]
  let relations := #["root", "nmod", "case"]
  let (forms, pos) := fixtureColumns heads.size
  ["In:Front", "In Front", "In|Front"].all fun marker ↦
    match enhanceArrays? heads relations forms #["Book", "Table", marker] pos with
    | .error _ => false
    | .ok result =>
        decide (result.counts = ⟨3, 0, 0⟩) && result.graph.edgeCount == 3

#guard invalidMarkerGolden

/-- Incoming propagation is direct-only and does not cross a nested `conj` governor. -/
private def directOnlyPropagationGolden : Bool :=
  let heads := #[0, 1, 2, 2, 4]
  let relations := #["root", "conj", "cc", "conj", "cc"]
  let lemmas := #["Run", "Jump", "And", "Skip", "Or"]
  let (forms, pos) := fixtureColumns heads.size
  match enhanceArrays? heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      decide (result.counts = ⟨5, 2, 1⟩) &&
        hasArc result 2 .root "root" .enhanced &&
        !hasArc result 4 .root "root" .enhanced

#guard directOnlyPropagationGolden

/-- Exact candidate, edge, and lexical-byte limits accept equality and diagnose one-short limits. -/
private def budgetBoundaries : Bool :=
  let heads := #[0, 1, 2, 2, 4]
  let relations := #["root", "obl", "case", "conj", "cc"]
  let lemmas := #["Met", "Home", "In", "Office", "And"]
  let (forms, pos) := fixtureColumns heads.size
  let exact : Config := { maxCandidates := 3, maxEdges := 8, maxLexicalBytes := 14 }
  let candidateShort : Config := { maxCandidates := 2, maxEdges := 8 }
  let edgeShort : Config := { maxCandidates := 3, maxEdges := 7 }
  let lexicalShort : Config :=
    { maxCandidates := 3, maxEdges := 8, maxLexicalBytes := 13 }
  let exactOk := (enhanceArraysWith? exact heads relations forms lemmas pos).isOk
  let candidateError :=
    match enhanceArraysWith? candidateShort heads relations forms lemmas pos with
    | .error (.candidateBudget 3 2) => true
    | _ => false
  let edgeError :=
    match enhanceArraysWith? edgeShort heads relations forms lemmas pos with
    | .error (.edgeBudget 8 7) => true
    | _ => false
  let lexicalError :=
    match enhanceArraysWith? lexicalShort heads relations forms lemmas pos with
    | .error (.lexicalBudget 14 13) => true
    | _ => false
  exactOk && candidateError && edgeError && lexicalError

#guard budgetBoundaries

/-- Lexical budgets count normalized UTF-8 bytes rather than characters. -/
private def unicodeLexicalBudget : Bool :=
  let heads := #[0, 1, 2]
  let relations := #["root", "nmod", "case"]
  let lemmas := #["root", "thing", "é"]
  let (forms, pos) := fixtureColumns heads.size
  let exact : Config := { maxCandidates := 1, maxEdges := 4, maxLexicalBytes := 7 }
  let short : Config := { maxCandidates := 1, maxEdges := 4, maxLexicalBytes := 6 }
  let exactOk :=
    match enhanceArraysWith? exact heads relations forms lemmas pos with
    | .ok result => hasArc result 2 (.word 1) "nmod:é" .enhanced
    | .error _ => false
  let shortError :=
    match enhanceArraysWith? short heads relations forms lemmas pos with
    | .error (.lexicalBudget 7 6) => true
    | _ => false
  exactOk && shortError

#guard unicodeLexicalBudget

/-- Disabled rule switches retain exactly the checked basic tree. -/
private def disabledRulesGolden : Bool :=
  let heads := #[0, 1, 2, 2, 4]
  let relations := #["root", "obl", "case", "conj", "cc"]
  let lemmas := #["Met", "Home", "In", "Office", "And"]
  let (forms, pos) := fixtureColumns heads.size
  let config : Config :=
    { lexicalizeNominals := false
      lexicalizeClauses := false
      lexicalizeConjunctions := false
      propagateIncomingConj := false }
  match enhanceArraysWith? config heads relations forms lemmas pos with
  | .error _ => false
  | .ok result =>
      decide (result.counts = ⟨5, 0, 0⟩) && result.graph.edgeCount == 5

#guard disabledRulesGolden

/-- Decode a base-`n` head function while omitting each dependent's self head. -/
private def headColumn (n code : Nat) : Array Nat :=
  Array.ofFn (n := n) fun index ↦
    let dependent := index.val + 1
    let digit := code / n ^ index.val % n
    if digit < dependent then digit else digit + 1

/-- Count accepted columns in the independent parent-function enumeration. -/
private def validHeadCount (n : Nat) : Nat := Id.run do
  let upper := if n = 0 then 1 else n ^ n
  let mut count := 0
  for code in [0:upper] do
    if (checkSentenceTree (headColumn n code)).isOk then
      count := count + 1
  return count

/-- Cayley's counts guard the completeness of the head-column generator through four words. -/
example :
    validHeadCount 0 = 1 ∧ validHeadCount 1 = 1 ∧ validHeadCount 2 = 2 ∧
      validHeadCount 3 = 9 ∧ validHeadCount 4 = 64 := by
  native_decide

/-- Assign deterministic valid root labels and varied non-root rule labels. -/
private def exhaustiveRelations (heads : Array Nat) : Array String :=
  Array.ofFn (n := heads.size) fun index ↦
    let dependent := index.val + 1
    let head := heads[index.val]!
    if head = 0 then
      "root"
    else
      match (3 * dependent + head) % 11 with
      | 0 => "conj"
      | 1 => "obl"
      | 2 => "nmod"
      | 3 => "acl"
      | 4 => "advcl"
      | 5 => "obj"
      | 6 => "case"
      | 7 => "mark"
      | 8 => "cc"
      | 9 => "fixed"
      | _ => "punct"

/-- Cycle mixed-case lemmas to exercise deterministic normalization. -/
private def exhaustiveLemmas (size : Nat) : Array String :=
  let vocabulary := #["In", "Front", "Of", "And", "Because"]
  Array.ofFn (n := size) fun index ↦ vocabulary[index.val % vocabulary.size]!

/-- Compare every valid head array through four words with the slow list oracle. -/
private def exhaustiveOracleParity : Bool := Id.run do
  for n in [0:5] do
    let upper := if n = 0 then 1 else n ^ n
    for code in [0:upper] do
      let heads := headColumn n code
      if (checkSentenceTree heads).isOk then
        let relations := exhaustiveRelations heads
        let lemmas := exhaustiveLemmas n
        let (forms, pos) := fixtureColumns n
        unless agreesWithOracle .default heads relations forms lemmas pos do
          return false
  return true

/-- Every valid parent function through four words agrees with the independent oracle. -/
example : exhaustiveOracleParity = true := by
  native_decide

/-- Result proofs expose exact public graph accounting to downstream callers. -/
example (result : Result) :
    result.graph.nodeCount = result.counts.basic ∧
      result.graph.edgeCount = result.counts.total :=
  ⟨result.nodeCount_eq, result.edgeCount_eq⟩

end NlpTests.Dependency.EnglishEnhanced
