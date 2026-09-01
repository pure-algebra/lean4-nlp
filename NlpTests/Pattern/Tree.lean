import Nlp.Pattern.Tree

/-! # Bounded typed tree-pattern tests -/

namespace NlpTests.Pattern.Tree

open Nlp Nlp.Syntax Nlp.Pattern.TreeQuery

/-- A branching tree that exercises every supported structural relation. -/
private def sample : NamedTree :=
  .node "S" (.node "NP" (.leaf "cats") #[])
    #[.node "VP" (.leaf "chase") #[.node "NP" (.leaf "mice") #[]]]

/-- Run one query through both checked compilation stages. -/
private def runItems (tree : NamedTree) (query : Query) : Option (Array TreeNodeId) := do
  let arena ← match TreeArena.ofNamedTree tree with
    | .ok value => some value
    | .error _ => none
  let compiled ← match compile query with
    | .ok value => some value
    | .error _ => none
  let result ← match findAll arena compiled with
    | .ok value => some value
    | .error _ => none
  return result.nodes

/-- All relation directions and deterministic preorder output agree with their intended meaning. -/
private def relationExamples : Bool :=
  runItems sample (.label "NP") == some #[1, 5] &&
    runItems sample (.child (.label "NP")) == some #[0, 3] &&
    runItems sample (.descendant (.label "mice")) == some #[0, 3, 5] &&
    runItems sample (.parent (.label "VP")) == some #[4, 5] &&
    runItems sample (.leftSibling (.label "NP")) == some #[3] &&
    runItems sample (.rightSibling (.label "VP")) == some #[1] &&
    runItems sample (.sibling (.label "NP")) == some #[3, 4] &&
    runItems sample (.precedes (.label "mice")) == some #[1, 2, 4] &&
    runItems sample (.follows (.label "cats")) == some #[3, 4, 5, 6] &&
    runItems sample
      (.both (.negate (.label "NP")) (.descendant (.label "mice"))) == some #[0, 3]

example : relationExamples = true := by native_decide

/-- A source-tree coordinate: zero selects the distinguished child, successors select siblings. -/
private abbrev SourcePath := List Nat

/-- Follow one source-tree coordinate without consulting `TreeArena`. -/
private def sourceAt? : NamedTree → SourcePath → Option NamedTree
  | tree, [] => some tree
  | .leaf _, _ :: _ => none
  | .node _ first rest, ordinal :: path =>
      if ordinal = 0 then sourceAt? first path
      else (rest[ordinal - 1]?).bind fun child => sourceAt? child path
  termination_by _ path => path.length

/-- Enumerate source paths directly in named-tree preorder with an explicit stack. -/
private def sourcePaths (tree : NamedTree) : Array SourcePath := Id.run do
  let mut output : Array SourcePath := #[]
  let mut stack : Array (NamedTree × SourcePath) := #[(tree, [])]
  while !stack.isEmpty do
    let (current, path) := stack.back!
    stack := stack.pop
    output := output.push path
    match current with
    | .leaf _ => pure ()
    | .node _ first rest =>
        for cursor in [0:rest.size] do
          let ordinal := rest.size - cursor
          stack := stack.push (rest[ordinal - 1]!, path ++ [ordinal])
        stack := stack.push (first, path ++ [0])
  return output

/-- Whether one source coordinate is a prefix of another. -/
private def pathPrefix : SourcePath → SourcePath → Bool
  | [], _ => true
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
      left == right && pathPrefix leftRest rightRest

/-- Immediate source parent coordinate. -/
private def parentPath? : SourcePath → Option SourcePath
  | [] => none
  | [_] => some []
  | first :: rest => (parentPath? rest).map (first :: ·)

/-- Final child ordinal in one nonroot source coordinate. -/
private def lastOrdinal? : SourcePath → Option Nat
  | [] => none
  | [ordinal] => some ordinal
  | _ :: rest => lastOrdinal? rest

/-- Source label at one coordinate. -/
private def sourceLabel? (tree : NamedTree) (path : SourcePath) : Option String :=
  (sourceAt? tree path).map fun
    | .leaf form => form
    | .node category _ _ => category

/-- Yield interval computed only from source-tree paths and source leaf constructors. -/
private def sourceYieldSpan? (tree : NamedTree) (paths : Array SourcePath)
    (anchor : SourcePath) : Option (Nat × Nat) := Id.run do
  let mut start : Option Nat := none
  let mut stop := 0
  let mut ordinal := 0
  for path in paths do
    match sourceAt? tree path with
    | some (.leaf _) =>
        if pathPrefix anchor path then
          if start.isNone then start := some ordinal
          stop := ordinal + 1
        ordinal := ordinal + 1
    | _ => pure ()
  return start.map fun first => (first, stop)

/-- Independent structural relation over source coordinates only. -/
private def sourceRelated (tree : NamedTree) (paths : Array SourcePath)
    (relation : Relation) (anchor target : SourcePath) : Bool :=
  if (sourceAt? tree anchor).isNone || (sourceAt? tree target).isNone then false
  else
    match relation with
    | .child => parentPath? target == some anchor
    | .descendant => anchor != target && pathPrefix anchor target
    | .parent => parentPath? anchor == some target
    | .leftSibling =>
        parentPath? anchor == parentPath? target &&
          (lastOrdinal? anchor).any fun anchorOrdinal =>
            lastOrdinal? target == some (anchorOrdinal - 1) && 0 < anchorOrdinal
    | .rightSibling =>
        parentPath? anchor == parentPath? target &&
          (lastOrdinal? anchor).any fun anchorOrdinal =>
            lastOrdinal? target == some (anchorOrdinal + 1)
    | .sibling =>
        anchor != target && parentPath? anchor == parentPath? target &&
          (parentPath? anchor).isSome
    | .precedes =>
        (sourceYieldSpan? tree paths anchor).any fun (_, anchorStop) =>
          (sourceYieldSpan? tree paths target).any fun (targetStart, _) =>
            anchorStop ≤ targetStart
    | .follows =>
        (sourceYieldSpan? tree paths anchor).any fun (anchorStart, _) =>
          (sourceYieldSpan? tree paths target).any fun (_, targetStop) =>
            targetStop ≤ anchorStart

/-- Recursive source-tree oracle, restricted to the exhaustive small trusted test slice. -/
private def sourceAccepts (tree : NamedTree) (paths : Array SourcePath)
    (anchor : SourcePath) : Query → Bool
  | .any => (sourceAt? tree anchor).isSome
  | .label expected => sourceLabel? tree anchor == some expected
  | .both left right =>
      sourceAccepts tree paths anchor left && sourceAccepts tree paths anchor right
  | .either left right =>
      sourceAccepts tree paths anchor left || sourceAccepts tree paths anchor right
  | .negate body =>
      (sourceAt? tree anchor).isSome && !sourceAccepts tree paths anchor body
  | .related relation target =>
      paths.any fun candidate =>
        sourceRelated tree paths relation anchor candidate &&
          sourceAccepts tree paths candidate target
  termination_by query => query

/-- Enumerate source-oracle matches as independent source preorder ordinals. -/
private def sourceFindAll (tree : NamedTree) (query : Query) : Array TreeNodeId := Id.run do
  let paths := sourcePaths tree
  let mut output := #[]
  for node in [0:paths.size] do
    if sourceAccepts tree paths paths[node]! query then output := output.push node
  return output

/-- Differential comparison between optimized evaluation and the independent scan oracle. -/
private def agrees (tree : NamedTree) (query : Query) : Bool :=
  match TreeArena.ofNamedTree tree, compile query with
  | .ok arena, .ok compiled =>
      match findAll arena compiled with
      | .ok result => result.nodes == sourceFindAll tree query
      | .error _ => false
  | _, _ => false

/-- Small nonempty tree shapes used by the exhaustive differential product. -/
private def smallTrees : Array NamedTree := #[
  .leaf "x",
  .node "R" (.leaf "x") #[],
  .node "R" (.leaf "x") #[.leaf "y"],
  .node "R" (.node "A" (.leaf "x") #[]) #[.node "B" (.leaf "y") #[]]
]

/-- Atom vocabulary for exhaustive bounded pattern generation. -/
private def atoms : Array Query := #[
  .any, .label "R", .label "A", .label "B", .label "x", .label "y", .label "z"
]

/-- Complete supported structural-relation vocabulary. -/
private def relations : Array Relation := #[
  .child, .descendant, .parent, .leftSibling, .rightSibling, .sibling, .precedes, .follows
]

/-- All atoms, unary forms, relations, and binary pairs up to this fixed small grammar slice. -/
private def smallQueries : Array Query := Id.run do
  let mut output := atoms
  for atom in atoms do
    output := output.push (.negate atom)
    for relation in relations do
      output := output.push (.related relation atom)
  for outer in relations do
    for inner in relations do
      output := output.push (.related outer (.related inner (.label "x")))
  for left in atoms do
    for right in atoms do
      output := output.push (.both left right)
      output := output.push (.either left right)
  return output

/-- Every generated query agrees on every generated nonempty tree. -/
private def exhaustiveAgreement : Bool :=
  smallTrees.all fun tree => smallQueries.all fun query => agrees tree query

example : exhaustiveAgreement = true := by native_decide

/-- A representative query with one indexed descendant operator. -/
private def budgetQuery : Query :=
  .both (.label "NP") (.descendant (.label "mice"))

/-- Compilation accepts equality and rejects one-short syntax and UTF-8 budgets exactly. -/
private def compileBudgets : Bool :=
  let exact := compileWith { maxPatternNodes := 4, maxTextBytes := 6 } budgetQuery
  let nodes := compileWith { maxPatternNodes := 3, maxTextBytes := 6 } budgetQuery
  let text := compileWith { maxPatternNodes := 4, maxTextBytes := 5 } budgetQuery
  exact.isOk &&
    (match nodes with
    | .error (.patternNodeBudget 4 3) => true
    | _ => false) &&
    (match text with
    | .error (.textBudget 6 5) => true
    | _ => false)

example : compileBudgets = true := by native_decide

/-- Work, indexed paths, and match retention all accept equality and reject one-short limits. -/
private def searchBudgets : Bool :=
  match TreeArena.ofNamedTree sample, compile budgetQuery with
  | .ok arena, .ok compiled =>
      let needed := requirements compiled arena
      match findAll arena compiled with
      | .error _ => false
      | .ok baseline =>
          let exact := findAllWith arena
            { maxWork := baseline.work, maxPaths := needed.paths,
              maxComparedBytes := baseline.comparedBytes, maxMatches := 1 } compiled
          let work := findAllWith arena
            { maxWork := baseline.work - 1, maxPaths := needed.paths,
              maxComparedBytes := baseline.comparedBytes, maxMatches := 1 } compiled
          let paths := findAllWith arena
            { maxWork := baseline.work, maxPaths := needed.paths - 1,
              maxComparedBytes := baseline.comparedBytes, maxMatches := 1 } compiled
          let bytes := findAllWith arena
            { maxWork := baseline.work, maxPaths := needed.paths,
              maxComparedBytes := baseline.comparedBytes - 1, maxMatches := 1 } compiled
          let matchRun := findAllWith arena
            { maxWork := baseline.work, maxPaths := needed.paths,
              maxComparedBytes := baseline.comparedBytes, maxMatches := 0 } compiled
          needed == { work := 60, paths := 28, comparedByteUpperBound := 164 } &&
            baseline.work == 60 && baseline.comparedBytes == 164 && exact.isOk &&
            (match work with
            | .error (.workBudget 60 59) => true
            | _ => false) &&
            (match paths with
            | .error (.pathBudget 28 27) => true
            | _ => false) &&
            (match bytes with
            | .error (.comparedByteBudget 164 163) => true
            | _ => false) &&
            (match matchRun with
            | .error (.matchBudget 1 0) => true
            | _ => false)
  | _, _ => false

example : searchBudgets = true := by native_decide

/-- Fixed exact-label byte accounting accepts equality and rejects one byte less preflight. -/
private def comparedBytePreflight : Bool :=
  match TreeArena.ofNamedTree sample, compile (.label "zzz") with
  | .ok arena, .ok compiled =>
      let needed := requirements compiled arena
      let exact := findAllWith arena
        { maxWork := needed.work, maxPaths := 0,
          maxComparedBytes := needed.comparedByteUpperBound, maxMatches := 0 } compiled
      let oneShort := findAllWith arena
        { maxWork := needed.work, maxPaths := 0,
          maxComparedBytes := needed.comparedByteUpperBound - 1, maxMatches := 0 } compiled
      needed.work == 15 && needed.comparedByteUpperBound == 82 && exact.isOk &&
        (match oneShort with
        | .error (.comparedByteBudget 82 81) => true
        | _ => false)
  | _, _ => false

example : comparedBytePreflight = true := by native_decide

/-- Expected optimized indexed-path charge for every relation on the seven-node sample. -/
private def relationPathCases : Array (Relation × Nat) := #[
  (.child, 13),
  (.descendant, 28),
  (.parent, 14),
  (.leftSibling, 14),
  (.rightSibling, 14),
  (.sibling, 28),
  (.precedes, 36),
  (.follows, 36)
]

/-- Every relation accepts its exact path formula and rejects a one-short path policy. -/
private def everyRelationPathFence : Bool :=
  match TreeArena.ofNamedTree sample with
  | .error _ => false
  | .ok arena => relationPathCases.all fun (relation, expected) =>
      match compile (.related relation .any) with
      | .error _ => false
      | .ok compiled =>
          let needed := requirements compiled arena
          let exact := findAllWith arena { maxPaths := expected } compiled
          let oneShort := findAllWith arena { maxPaths := expected - 1 } compiled
          needed.paths == expected && exact.isOk &&
            (match oneShort with
            | .error (.pathBudget required limit) =>
                required == expected && limit == expected - 1
            | _ => false)

example : everyRelationPathFence = true := by native_decide

/-- The compiled type index exposes its exact caller query without a reconstruction pass. -/
example (compiled : Compiled budgetQuery) : compiled.sourceQuery = budgetQuery :=
  compiled.sourceQuery_eq

/-- The privately cached independent program retains its exact-source certificate. -/
example (compiled : Compiled budgetQuery) : compiled.IndependentWF :=
  compiled.independentWellFormed

/-- Every public match carries both node validity and direct-source-query acceptance. -/
example (matched : Match arena query config) : matched.WF := matched.wellFormed

/-- Build a deeply nested boolean query without recursive construction. -/
private def deepNegation (depth : Nat) : Query := Id.run do
  let mut query := Query.any
  for _ in [0:depth] do query := .negate query
  return query

/-- Explicit compiler frames handle hostile pattern depth at the exact node cap. -/
example :
    (compileWith { maxPatternNodes := 8_193, maxTextBytes := 0 }
      (deepNegation 8_192)).isOk = true := by
  native_decide

/-- Postfix evaluation also handles hostile pattern depth without recursive calls. -/
private def deepEvaluation : Bool :=
  match TreeArena.ofNamedTree (.leaf "x"),
      compileWith { maxPatternNodes := 8_193, maxTextBytes := 0 }
        (deepNegation 8_192) with
  | .ok arena, .ok compiled =>
      match findAllWith arena
          { maxWork := 24_579, maxPaths := 0, maxComparedBytes := 0,
            maxMatches := 1 } compiled with
      | .ok result => result.nodes == #[0]
      | .error _ => false
  | _, _ => false

example : deepEvaluation = true := by native_decide

end NlpTests.Pattern.Tree
