import Nlp.Pattern.Graph

/-!
# Typed dependency-graph pattern tests

These checks exercise exact index budgets, both direct-edge directions, boolean composition,
named-node equality, deterministic result order, and exact runtime work/output limits.
-/

namespace NlpTests.Pattern.Graph

open Nlp.Dependency Nlp.Pattern Nlp.Pattern.GraphQuery

/-- A reentrant three-word graph with two differently labeled edges to its object. -/
private def graph : Except (GraphError String) (Nlp.Dependency.Graph String) :=
  Nlp.Dependency.Graph.ofRows
    #[⟨.word 1, #[⟨.word 2, "nsubj", .basic⟩]⟩,
      ⟨.word 2, #[⟨.root, "root", .basic⟩]⟩,
      ⟨.word 3,
        #[⟨.word 2, "obj", .basic⟩, ⟨.word 2, "theme", .enhanced⟩]⟩]

/-- Optional token columns aligned with the three stored graph nodes. -/
private def attributes : Array NodeAttributes :=
  #[{ form := some "Alice", pos := some "PROPN", lemma := some "Alice",
      ner := some "PERSON" },
    { form := some "likes", pos := some "VERB", lemma := some "like", ner := some "O" },
    { form := some "pizza", pos := some "NOUN", lemma := some "pizza", ner := some "FOOD" }]

/-- Checked dual index used by the query regression tests. -/
private def index : Except IndexError Index := do
  match graph with
  | .error _ => throw .inconsistentStorage
  | .ok source => Index.compile source attributes

/-- A sparse identifier just beyond the default 32-bit coordinate policy. -/
private def wideCoordinateGraph : Except (GraphError String) (Nlp.Dependency.Graph String) :=
  Nlp.Dependency.Graph.ofRows
    #[⟨.word 4_294_967_296, #[⟨.root, "root", .basic⟩]⟩]

/-- Canonical nodes separated by 2^64, an adversarial pattern for fixed-width hashes. -/
private def collisionCoordinateGraph : Except (GraphError String)
    (Nlp.Dependency.Graph String) := Id.run do
  let stride := 18_446_744_073_709_551_616
  let mut rows : Array (Row String) := #[]
  for ordinal in [0:9] do
    rows := rows.push
      ⟨.word (1 + ordinal * stride), #[⟨.root, "root", .basic⟩]⟩
  return Nlp.Dependency.Graph.ofRows rows

/-- Word, copy, and empty nodes sharing one major coordinate in canonical kind order. -/
private def mixedKindGraph : Except (GraphError String) (Nlp.Dependency.Graph String) :=
  Nlp.Dependency.Graph.ofRows
    #[⟨.word 1, #[⟨.root, "root", .basic⟩]⟩,
      ⟨.copy 1 1, #[⟨.root, "root", .copy⟩]⟩,
      ⟨.empty 1 1, #[⟨.root, "root", .empty⟩]⟩]

/-- Read compact result coordinates for deterministic assertions. -/
private def coordinates {index : Index} (result : Result index config) :
    Array (NodeId × Array (String × NodeId)) :=
  result.items.map fun matched ↦
    (matched.anchor, matched.bindings.map fun binding ↦ (binding.name, binding.node))

/-- Direct incoming and outgoing constraints select the verb and retain stable named nodes. -/
private def transitiveQuery : Query :=
  .bind "verb" <| .both (.node (.attribute .lemma "like")) <|
    .both
      (.outgoing (.equal "nsubj") <|
        .bind "subject" (.node (.attribute .ner "PERSON")))
      (.outgoing (.equal "obj") <|
        .bind "object" (.node (.attribute .form "pizza")))

/-- A finite basis covering every constructor in the direct-edge query algebra. -/
private def primitiveQueries : Array Query :=
  #[.node .any,
    .node .root,
    .node (.node (.word 2)),
    .node (.attribute .form "Alice"),
    .node (.attribute .pos "VERB"),
    .node (.attribute .lemma "like"),
    .node (.attribute .ner "FOOD"),
    .node (.both (.attribute .pos "VERB") (.attribute .lemma "like")),
    .node (.either .root (.attribute .ner "PERSON")),
    .node (.negate (.attribute .ner "O")),
    .incoming .any (.node .any),
    .incoming (.prefix "n") (.node .any),
    .outgoing (.suffix "j") (.node .any),
    .outgoing (.oneOf #["obj", "theme"]) (.node .any),
    .bind "self" (.same "self"),
    .same "missing",
    .negate (.outgoing (.equal "obl") (.node .any))]

/-- Exhaust every depth-one boolean composition over the finite constructor basis. -/
private def parityQueries : Array Query := Id.run do
  let mut queries := primitiveQueries.push transitiveQuery
  for left in primitiveQueries do
    for right in primitiveQueries do
      queries := queries.push (.both left right)
      queries := queries.push (.either left right)
  return queries

/-- Build many distinct bindings without relying on general recursion. -/
private def bindMany : Nat → Query → Query
  | 0, body => body
  | count + 1, body => .bind s!"node{count}" (bindMany count body)

/-- Build a deeply nested recursive predicate for stack-policy regression tests. -/
private def nestedPredicate : Nat → NodePredicate
  | 0 => .any
  | depth + 1 => .negate (nestedPredicate depth)

/-- Every string-bearing graph-query form, with repeated syntax occurrences counted separately. -/
private def lexicalQuery : Query :=
  .bind "anchor" <| .both (.node (.attribute .lemma "like")) <|
    .both (.same "anchor") <|
      .both
        (.outgoing (.equal "obj") (.node (.attribute .form "pizza"))) <|
        .both
          (.outgoing (.prefix "th") (.node .any)) <|
          .both
            (.outgoing (.suffix "me") (.node .any))
            (.outgoing (.oneOf #["obj", "theme"]) (.node .any))

#guard
  match index with
  | .error _ => false
  | .ok checked =>
      match findAll checked transitiveQuery with
      | .error _ => false
      | .ok found =>
          coordinates found ==
            #[(.word 2,
              #[
                ("verb", .word 2),
                ("subject", .word 1),
                ("object", .word 3)])]

-- The optimized dual-index evaluator equals the slow row-scan denotation on the complete finite
-- depth-one boolean algebra generated above.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      parityQueries.all fun query =>
        match findAll checked query with
        | .error _ => false
        | .ok optimized => optimized.referenceView == referenceFindAll checked query

-- Outgoing matches retain canonical dependent-row and then relation order.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let query := .both (.node (.node (.word 2))) <|
        .outgoing .any (.bind "dependent" (.node .any))
      match findAll checked query with
      | .error _ => false
      | .ok found =>
          coordinates found ==
            #[(.word 2, #[("dependent", .word 1)]),
              (.word 2, #[("dependent", .word 3)]),
              (.word 2, #[("dependent", .word 3)])]

-- Root and contiguous ordinary words use the direct dense fast path, including absent probes.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      checked.denseOf? .root == some 0 &&
        checked.denseOf? (.word 1) == some 1 &&
        checked.denseOf? (.word 2) == some 2 &&
        checked.denseOf? (.word 3) == some 3 &&
        checked.denseOf? (.word 4) == none

-- Copy/empty nodes and a displaced word exercise the canonical binary fallback.
#guard
  match mixedKindGraph with
  | .error _ => false
  | .ok source =>
      match Index.compileGraph source with
      | .error _ => false
      | .ok checked =>
          checked.denseOf? (.word 1) == some 1 &&
            checked.denseOf? (.copy 1 1) == some 2 &&
            checked.denseOf? (.empty 1 1) == some 3 &&
            checked.denseOf? (.word 2) == none &&
            checked.denseOf? (.copy 1 2) == none &&
            checked.denseOf? (.empty 1 2) == none

-- A contiguous word match charges its direct probe and certificate replay exactly once each.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let query : Query := .node (.node (.word 2))
      let exact : SearchConfig := { maxWork := 13 }
      let low : SearchConfig := { maxWork := 12 }
      let exactAccepted :=
        match findAllWith checked exact query with
        | .ok result => result.items.size == 1 && result.work == 13
        | _ => false
      let lowRejected :=
        match findAllWith checked low query with
        | .error (.workBudget required limit) => required == 13 && limit == 12
        | _ => false
      exactAccepted && lowRejected

-- Incoming direction follows a dependent edge back to its governor.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      match findAll checked <|
          .both (.node (.attribute .form "Alice"))
            (.incoming (.equal "nsubj") <|
              .node (.attribute .lemma "like")) with
      | .ok found =>
          match found.items[0]? with
          | some matched => found.items.size == 1 && matched.anchor == .word 1
          | none => false
      | .error _ => false

-- Reusing a name is a node-identity backreference rather than a second independent binding.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      match findAll checked <|
          .both (.node (.attribute .lemma "like")) <|
            .both
              (.outgoing (.equal "obj") <| .bind "argument" (.node .any))
              (.outgoing (.equal "theme") <| .same "argument") with
      | .ok found =>
          match found.items[0]? with
          | some matched =>
              found.items.size == 1 && matched.binding? "argument" == some (.word 3)
          | none => false
      | .error _ => false

-- A mismatched backreference rejects a structurally similar pair of outgoing edges.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      match findAll checked <|
          .both (.node (.attribute .lemma "like")) <|
            .both
              (.outgoing (.equal "nsubj") <| .bind "argument" (.node .any))
              (.outgoing (.equal "obj") <| .same "argument") with
      | .ok found => found.items.isEmpty
      | .error _ => false

-- Root, negation, and exact optional-attribute predicates compose without special cases.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let rootQuery := .both (.node .root) <|
        .outgoing (.equal "root") (.node (.attribute .pos "VERB"))
      let verbQuery := .both (.node (.attribute .lemma "like")) <|
        .negate (.outgoing (.equal "obl") (.node .any))
      match findAll checked rootQuery, findAll checked verbQuery with
      | .ok roots, .ok verbs =>
          match roots.items[0]?, verbs.items[0]? with
          | some root, some verb =>
              roots.items.size == 1 && root.anchor == .root &&
                verbs.items.size == 1 && verb.anchor == .word 2
          | _, _ => false
      | _, _ => false

-- Index node, edge, text, and coordinate limits accept exact requirements and reject one less.
#guard
  match graph with
  | .error _ => false
  | .ok source =>
      let bytes := requiredLexicalBytes source attributes
      let coordinate := requiredCoordinate source
      let exact : IndexConfig :=
        { maxNodes := source.nodeCount, maxEdges := source.edgeCount,
          maxLexicalBytes := bytes, maxCoordinate := coordinate }
      let nodeLow := { exact with maxNodes := source.nodeCount - 1 }
      let edgeLow := { exact with maxEdges := source.edgeCount - 1 }
      let byteLow := { exact with maxLexicalBytes := bytes - 1 }
      let coordinateLow := { exact with maxCoordinate := coordinate - 1 }
      let nodeRejected :=
        match Index.compileWith nodeLow source attributes with
        | .error (.nodeBudget required limit) =>
            required == source.nodeCount && limit == nodeLow.maxNodes
        | _ => false
      let edgeRejected :=
        match Index.compileWith edgeLow source attributes with
        | .error (.edgeBudget required limit) =>
            required == source.edgeCount && limit == edgeLow.maxEdges
        | _ => false
      let byteRejected :=
        match Index.compileWith byteLow source attributes with
        | .error (.lexicalByteBudget required limit) =>
            required == bytes && limit == byteLow.maxLexicalBytes
        | _ => false
      let coordinateRejected :=
        match Index.compileWith coordinateLow source attributes with
        | .error (.coordinateBudget required limit) =>
            required == coordinate && limit == coordinate - 1
        | _ => false
      (Index.compileWith exact source attributes).isOk && nodeRejected && edgeRejected &&
        byteRejected && coordinateRejected

-- Attribute-free compilation rejects graph limits before allocating its default attribute column.
#guard
  match graph with
  | .error _ => false
  | .ok source =>
      let bytes := requiredLexicalBytes source #[]
      let exact : IndexConfig :=
        { maxNodes := source.nodeCount, maxEdges := source.edgeCount,
          maxLexicalBytes := bytes }
      let nodeRejected :=
        match Index.compileGraphWith { exact with maxNodes := source.nodeCount - 1 } source with
        | .error (.nodeBudget required limit) =>
            required == source.nodeCount && limit == source.nodeCount - 1
        | _ => false
      let edgeRejected :=
        match Index.compileGraphWith { exact with maxEdges := source.edgeCount - 1 } source with
        | .error (.edgeBudget required limit) =>
            required == source.edgeCount && limit == source.edgeCount - 1
        | _ => false
      let byteRejected :=
        match Index.compileGraphWith { exact with maxLexicalBytes := bytes - 1 } source with
        | .error (.lexicalByteBudget required limit) =>
            required == bytes && limit == bytes - 1
        | _ => false
      (Index.compileGraphWith exact source).isOk && nodeRejected && edgeRejected && byteRejected

-- The default coordinate width rejects 2^32, while an explicit wider policy accepts it exactly.
#guard
  match wideCoordinateGraph with
  | .error _ => false
  | .ok source =>
      let wide := 4_294_967_296
      let defaultRejected :=
        match Index.compileGraph source with
        | .error (.coordinateBudget required limit) =>
            required == wide && limit == wide - 1
        | _ => false
      let exact : IndexConfig := { maxCoordinate := wide }
      defaultRejected && (Index.compileGraphWith exact source).isOk

-- Sparse fixed-width hash-collision coordinates use the canonical binary fallback.
#guard
  match collisionCoordinateGraph with
  | .error _ => false
  | .ok source =>
      let stride := 18_446_744_073_709_551_616
      let maximum := 1 + 8 * stride
      match Index.compileGraphWith { maxCoordinate := maximum } source with
      | .error _ => false
      | .ok checked =>
          let target := .word (1 + stride)
          let search : SearchConfig :=
            { maxWork := 29, maxQueryCoordinate := maximum }
          let low := { search with maxWork := 28 }
          let exactAccepted :=
            match findAllWith checked search (.node (.node target)) with
            | .ok result => result.items.size == 1 && result.work == 29
            | _ => false
          let lowRejected :=
            match findAllWith checked low (.node (.node target)) with
            | .error (.workBudget required limit) => required == 29 && limit == 28
            | _ => false
          (Array.range 9).all (fun ordinal =>
            checked.denseOf? (.word (1 + ordinal * stride)) == some (ordinal + 1)) &&
            checked.denseOf? (.word (2 + stride)) == none && exactAccepted && lowRejected

-- Exact query lexical requirements count each binding/backreference, attribute value, relation
-- test, and `oneOf` value occurrence once; a one-short byte policy rejects the exact total.
#guard
  match lexicalQuery.requirements, index with
  | .ok needed, .ok checked =>
      let low : SearchConfig := { maxQueryLexicalBytes := needed.lexicalBytes - 1 }
      let requirementsRejected :=
        match lexicalQuery.requirementsWith low with
        | .error (.queryLexicalByteBudget required limit) =>
            required == needed.lexicalBytes && limit == needed.lexicalBytes - 1
        | _ => false
      let searchRejected :=
        match findAllWith checked low lexicalQuery with
        | .error (.queryLexicalByteBudget required limit) =>
            required == needed.lexicalBytes && limit == needed.lexicalBytes - 1
        | _ => false
      needed.lexicalBytes == 36 && requirementsRejected && searchRejected
  | _, _ => false

-- Query, predicate, relation-choice, and combined-depth budgets accept exact shape and reject one
-- less; an oversized caller depth request cannot bypass the hard evaluator cap.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let shaped := .outgoing (.oneOf #["obj", "theme"]) (.node .any)
      let exact : SearchConfig := { maxQueryNodes := 6, maxQueryDepth := 3 }
      let nodeLow := { exact with maxQueryNodes := 5 }
      let depthLow := { exact with maxQueryDepth := 2 }
      let hard : SearchConfig := { maxQueryNodes := 300, maxQueryDepth := 10_000 }
      let nodeRejected :=
        match findAllWith checked nodeLow shaped with
        | .error (.queryNodeBudget required limit) => required == 6 && limit == 5
        | _ => false
      let depthRejected :=
        match findAllWith checked depthLow shaped with
        | .error (.queryDepthBudget required limit) => required == 3 && limit == 2
        | _ => false
      let hardRejected :=
        match findAllWith checked hard (.node (nestedPredicate 255)) with
        | .error (.queryDepthBudget required limit) => required == 257 && limit == 256
        | _ => false
      (findAllWith checked exact shaped).isOk && nodeRejected && depthRejected && hardRejected

-- Query node coordinates have an exact default 32-bit boundary and explicit wider opt-in.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let wide := 4_294_967_296
      let query : Query := .node (.node (.word wide))
      let exact : SearchConfig := { maxQueryCoordinate := wide }
      let low : SearchConfig := { maxQueryCoordinate := wide - 1 }
      let exactAccepted :=
        match query.requirementsWith exact, findAllWith checked exact query with
        | .ok requirements, .ok result =>
            requirements.coordinateMaximum == wide && result.items.isEmpty
        | _, _ => false
      let lowRejected :=
        match findAllWith checked low query with
        | .error (.queryCoordinateBudget required limit) =>
            required == wide && limit == wide - 1
        | _ => false
      let defaultRejected :=
        match findAll checked query with
        | .error (.queryCoordinateBudget required limit) =>
            required == wide && limit == wide - 1
        | _ => false
      exactAccepted && lowRejected && defaultRejected

-- Standalone predicates are bounded and closed over valid dense nodes, including under negation.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let invalidClosed :=
        match NodePredicate.accepts checked 99 (.negate .any) with
        | .ok false => true
        | _ => false
      let low : SearchConfig := { maxQueryNodes := 4, maxQueryDepth := 2 }
      let depthRejected :=
        match NodePredicate.acceptsWith checked low 0 (nestedPredicate 1) with
        | .error (.queryDepthBudget required limit) => required == 3 && limit == 2
        | _ => false
      invalidClosed && checked.nodeAt? 99 == none && depthRejected

-- Empty definitions and empty backreferences are rejected before recursive evaluation.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let bindRejected :=
        match findAll checked (.bind "" (.node .any)) with
        | .error .emptyBindingName => true
        | _ => false
      let sameRejected :=
        match findAll checked (.same "") with
        | .error .emptyBindingName => true
        | _ => false
      bindRejected && sameRejected

-- Attribute comparisons charge both complete UTF-8 operands, with an exact one-short failure.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let query : Query := .node (.attribute .form "pizza")
      let exact : SearchConfig := { maxComparisonBytes := 30 }
      let low : SearchConfig := { maxComparisonBytes := 29 }
      let exactAccepted :=
        match findAllWith checked exact query with
        | .ok result =>
            result.comparisonBytes == 30 &&
              decide (result.comparisonBytes ≤ exact.maxComparisonBytes)
        | .error _ => false
      let lowRejected :=
        match findAllWith checked low query with
        | .error (.comparisonByteBudget required limit) => required == 30 && limit == 29
        | _ => false
      exactAccepted && lowRejected

-- Relation equality, prefix, suffix, and every visited `oneOf` choice charge both operands.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let compared (test : TextTest) : Option Nat := do
        let result ← (findAll checked (.outgoing test (.node .any))).toOption
        return result.comparisonBytes
      compared (.equal "obj") == some 29 &&
        compared (.prefix "n") == some 21 &&
        compared (.suffix "j") == some 21 &&
        compared (.oneOf #["missing", "obj"]) == some 74

-- Binding lookup comparisons have an exact byte charge; one binding has no sealing name pairs.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let query : Query := .bind "x" (.same "x")
      let exact : SearchConfig := { maxComparisonBytes := 8 }
      let low : SearchConfig := { maxComparisonBytes := 7 }
      let exactAccepted :=
        match findAllWith checked exact query with
        | .ok result => result.items.size == 4 && result.comparisonBytes == 8
        | .error _ => false
      let lowRejected :=
        match findAllWith checked low query with
        | .error (.comparisonByteBudget required limit) => required == 8 && limit == 7
        | _ => false
      exactAccepted && lowRejected

-- Negation stops at its first witness and does not retain an array that it immediately discards.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let query : Query := .negate (.outgoing .any (.node .any))
      let exact : SearchConfig := { maxStates := 4 }
      let low : SearchConfig := { maxStates := 3 }
      let exactAccepted :=
        match findAllWith checked exact query with
        | .ok result =>
            result.states == 4 && result.referenceView == referenceFindAll checked query
        | .error _ => false
      let lowRejected :=
        match findAllWith checked low query with
        | .error (.stateBudget required limit) => required == 4 && limit == 3
        | _ => false
      exactAccepted && lowRejected

-- Checked-query cursors preserve provenance, monolithic counters, and canonical result order.
#guard
  match index, transitiveQuery.check with
  | .ok checked, .ok compiled =>
      let cursor := SearchCursor.startChecked checked compiled
      match cursor.advanceBy checked.nodeCount with
      | .error _ => false
      | .ok completed =>
          match completed.result?, findAllCheckedWith checked compiled,
              findAll checked transitiveQuery with
          | some resumed, .ok checkedDirect, .ok rawDirect =>
              decide (resumed.query = transitiveQuery) &&
                resumed.referenceView == checkedDirect.referenceView &&
                resumed.referenceView == rawDirect.referenceView &&
                resumed.work == rawDirect.work && resumed.states == rawDirect.states &&
                resumed.comparisonBytes == rawDirect.comparisonBytes
          | _, _, _ => false
  | _, _ => false

-- The sealed index exposes its checked lexical total without recomputing source columns.
#guard
  match graph, index with
  | .ok source, .ok checked => checked.lexicalBytes == requiredLexicalBytes source attributes
  | _, _ => false

-- Many bindings preserve the reference denotation and make the charged sealing tail observable.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      let query := bindMany 32 (.node .any)
      match findAll checked query with
      | .error _ => false
      | .ok baseline =>
          let workLow : SearchConfig := { maxWork := baseline.work - 1 }
          let bytesExact : SearchConfig :=
            { maxComparisonBytes := baseline.comparisonBytes }
          let bytesLow : SearchConfig :=
            { maxComparisonBytes := baseline.comparisonBytes - 1 }
          let workOneShort :=
            match findAllWith checked workLow query with
            | .error (.workBudget required limit) =>
                required == baseline.work && limit == baseline.work - 1
            | _ => false
          let bytesOneShort :=
            match findAllWith checked bytesLow query with
            | .error (.comparisonByteBudget required limit) =>
                required == baseline.comparisonBytes &&
                  limit == baseline.comparisonBytes - 1
            | _ => false
          baseline.items.all (fun matched => matched.bindings.size == 32) &&
            baseline.comparisonBytes == 45_136 &&
            baseline.referenceView == referenceFindAll checked query &&
            (findAllWith checked bytesExact query).isOk && workOneShort && bytesOneShort

-- Runtime work and result bounds report the exact first forbidden unit.
#guard
  match index with
  | .error _ => false
  | .ok checked =>
      match findAll checked transitiveQuery with
      | .error _ => false
      | .ok baseline =>
          let lowWork : SearchConfig :=
            { maxWork := baseline.work - 1, maxMatches := 8 }
          let lowStates : SearchConfig :=
            { maxWork := baseline.work, maxStates := baseline.states - 1, maxMatches := 1 }
          let exactWork : SearchConfig :=
            { maxWork := baseline.work, maxStates := baseline.states, maxMatches := 1 }
          let noMatches : SearchConfig :=
            { maxWork := baseline.work, maxMatches := 0 }
          let workRejected :=
            match findAllWith checked lowWork transitiveQuery with
            | .error (.workBudget required limit) =>
                required == baseline.work && limit == lowWork.maxWork
            | _ => false
          let matchRejected :=
            match findAllWith checked noMatches transitiveQuery with
            | .error (.matchBudget required limit) => required == 1 && limit == 0
            | _ => false
          let stateRejected :=
            match findAllWith checked lowStates transitiveQuery with
            | .error (.stateBudget required limit) =>
                required == baseline.states && limit == baseline.states - 1
            | _ => false
          workRejected && stateRejected &&
            (findAllWith checked exactWork transitiveQuery).isOk && matchRejected

end NlpTests.Pattern.Graph
