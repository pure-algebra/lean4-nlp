import Nlp.Core.Data.DependencyGraph

/-! # Checked enhanced-dependency graph tests -/

namespace NlpTests.Core.DependencyGraph

open Nlp.Dependency

/-- Build a concise string-labeled arc for test rows. -/
private def arc (head : NodeId) (relation : String)
    (origin : Origin := .enhanced) : Arc String :=
  ⟨head, relation, origin⟩

/-- Build a concise string-labeled incoming row. -/
private def row (dependent : NodeId) (incoming : Array (Arc String)) : Row String :=
  ⟨dependent, incoming⟩

/-- A graph containing reentrancy, a directed cycle, and two root dependents. -/
private def richRows : Array (Row String) :=
  #[row (.word 1) #[arc .root "root" .basic],
    row (.word 2) #[arc .root "root" .basic, arc (.word 3) "back"],
    row (.word 3) #[arc (.word 1) "branch", arc (.word 2) "cycle"]]

/- Reentrancy, cycles, and multiple root arcs are all accepted together. -/
#guard match Graph.ofRows richRows with
  | .ok graph =>
    graph.nodeCount == 3 && graph.edgeCount == 5 &&
      graph.nodes == #[.word 1, .word 2, .word 3]
  | .error _ => false

/-- Incoming lookup reconstructs one exact CSR row. -/
example :
    (Graph.ofRows richRows).toOption.bind (fun graph ↦ graph.incoming? (.word 3)) =
      some (row (.word 3) #[arc (.word 1) "branch", arc (.word 2) "cycle"]) := by
  native_decide

/-- Converting checked CSR storage back to rows is lossless. -/
example : (Graph.ofRows richRows).toOption.map Graph.toRows = some richRows := by
  native_decide

/-- The proof accessor exposes checker success for every constructible graph. -/
example (graph : Graph String) : graph.WF := graph.wellFormed

/- Root, empty, word, copied, and later empty nodes follow canonical position order. -/
#guard NodeId.compare .root (.empty 0 1) == .lt
#guard NodeId.compare (.empty 0 1) (.word 1) == .lt
#guard NodeId.compare (.word 1) (.copy 1 1) == .lt
#guard NodeId.compare (.copy 1 1) (.empty 1 1) == .lt
#guard NodeId.compare (.empty 1 1) (.word 2) == .lt

/- Every valid node family can coexist in one checked graph. -/
#guard match Graph.ofRows
    #[row (.empty 0 1) #[arc .root "root"],
      row (.word 1) #[arc .root "root"],
      row (.copy 1 1) #[arc .root "root"],
      row (.empty 1 1) #[arc .root "root"],
      row (.word 2) #[arc .root "root"]] with
  | .ok graph =>
    graph.nodes ==
      #[.empty 0 1, .word 1, .copy 1 1, .empty 1 1, .word 2]
  | .error _ => false

/- Distinct relations permit parallel arcs with the same head. -/
#guard (Graph.ofRows
  #[row (.word 1) #[arc .root "a", arc .root "b"]]).isOk

/- Aggregate storage accounting includes nodes, offsets, and all three edge columns. -/
#guard Graph.requiredEntries 1 1 == 6

/- An exact aggregate-entry budget is accepted. -/
#guard (Graph.ofRowsWith { maxEntries := 6 }
  #[row (.word 1) #[arc .root "root"]]).isOk

/- A one-entry-short budget reports both the exact requirement and limit. -/
#guard match Graph.ofRowsWith { maxEntries := 5 }
    #[row (.word 1) #[arc .root "root"]] with
  | .error (.entryBudget 6 5) => true
  | _ => false

/- Empty graphs retain exactly their initial offset and fit a one-entry budget. -/
#guard match Graph.ofRowsWith (R := String) { maxEntries := 1 } #[] with
  | .ok graph => graph.nodeCount == 0 && graph.edgeCount == 0
  | .error _ => false

/- The empty graph fails an aggregate-entry budget of zero at the exact boundary. -/
#guard match Graph.ofRowsWith (R := String) { maxEntries := 0 } #[] with
  | .error (.entryBudget 1 0) => true
  | _ => false

/- The artificial root cannot be stored as a dependent. -/
#guard match Graph.ofRows #[row .root #[arc .root "root"]] with
  | .error (.rootNode 0) => true
  | _ => false

/- Ordinary word coordinates are strictly positive. -/
#guard match Graph.ofRows #[row (.word 0) #[arc .root "root"]] with
  | .error (.invalidNode (.word 0)) => true
  | _ => false

/- Empty-node minor coordinates are strictly positive. -/
#guard match Graph.ofRows #[row (.empty 1 0) #[arc .root "root"]] with
  | .error (.invalidNode (.empty 1 0)) => true
  | _ => false

/- Copied-node word coordinates are strictly positive. -/
#guard match Graph.ofRows #[row (.copy 0 1) #[arc .root "root"]] with
  | .error (.invalidNode (.copy 0 1)) => true
  | _ => false

/- Copied-node minor coordinates are strictly positive. -/
#guard match Graph.ofRows #[row (.copy 1 0) #[arc .root "root"]] with
  | .error (.invalidNode (.copy 1 0)) => true
  | _ => false

/- Invalid positive-coordinate rules also apply to heads. -/
#guard match Graph.ofRows #[row (.word 1) #[arc (.word 0) "bad"]] with
  | .error (.invalidNode (.word 0)) => true
  | _ => false

/- Dependents must be strictly ordered, so duplicate rows fail the same check. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc .root "a"], row (.word 1) #[arc .root "b"]] with
  | .error (.nodeOrder (.word 1) (.word 1)) => true
  | _ => false

/- Descending dependent order retains the adjacent witness. -/
#guard match Graph.ofRows
    #[row (.word 2) #[arc .root "a"], row (.word 1) #[arc .root "b"]] with
  | .error (.nodeOrder (.word 2) (.word 1)) => true
  | _ => false

/- Every non-root head must be present in the dependent node set. -/
#guard match Graph.ofRows #[row (.word 1) #[arc (.word 2) "missing"]] with
  | .error (.missingHead (.word 1) (.word 2)) => true
  | _ => false

/- Self-governing arcs are rejected before root and reachability checks. -/
#guard match Graph.ofRows #[row (.word 1) #[arc (.word 1) "self"]] with
  | .error (.selfEdge (.word 1)) => true
  | _ => false

/- Exact head-and-relation duplicates ignore provenance. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc .root "root" .basic, arc .root "root"]] with
  | .error (.duplicateArc (.word 1) .root "root") => true
  | _ => false

/- Incoming head order is checked independently of dependent order. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc (.word 2) "dep", arc .root "root"],
      row (.word 2) #[arc .root "root"]] with
  | .error (.incomingOrder (.word 1) (.word 2) "dep" .root "root") => true
  | _ => false

/- Relations under a shared head must also be strictly ordered. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc .root "z", arc .root "a"]] with
  | .error (.incomingOrder (.word 1) .root "z" .root "a") => true
  | _ => false

/- A nonempty rootless cycle is rejected even though all heads resolve. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc (.word 2) "cycle"],
      row (.word 2) #[arc (.word 1) "cycle"]] with
  | .error .noRoot => true
  | _ => false

/- A disconnected cycle retains the first unreachable node in canonical order. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc .root "root"],
      row (.word 2) #[arc (.word 3) "cycle"],
      row (.word 3) #[arc (.word 2) "cycle"]] with
  | .error (.unreachable (.word 2)) => true
  | _ => false

/- Parallel edge columns must remain aligned. -/
#guard match Graph.checkCSR #[.word 1] #[0, 1] #[.root]
    (#[] : Array String) #[.basic] with
  | .error (.columnCount 1 0 1) => true
  | _ => false

/- CSR requires one more offset than stored dependent nodes. -/
#guard match Graph.checkCSR #[.word 1] #[0] #[.root] #["root"] #[.basic] with
  | .error (.offsetCount 2 1) => true
  | _ => false

/- CSR offsets must begin at zero. -/
#guard match Graph.checkCSR #[.word 1] #[1, 1] #[.root] #["root"] #[.basic] with
  | .error (.invalidOffset 0 1 1 1) => true
  | _ => false

/- Every stored dependent must have a nonempty incoming row. -/
#guard match Graph.ofRows #[row (.word 1) #[]] with
  | .error (.invalidOffset 0 0 0 0) => true
  | _ => false

/- A row stop cannot exceed the aligned edge-column length. -/
#guard match Graph.checkCSR #[.word 1] #[0, 2] #[.root] #["root"] #[.basic] with
  | .error (.invalidOffset 0 0 2 1) => true
  | _ => false

/- The final offset must consume every aligned edge entry. -/
#guard match Graph.checkCSR #[.word 1] #[0, 1] #[.root, .root]
    #["a", "b"] #[.basic, .basic] with
  | .error (.invalidOffset 1 1 1 2) => true
  | _ => false

/-- A checked tree converts to aligned basic-origin CSR columns. -/
private def treeConversionOk : Bool :=
  match Tree.ofArrays #[0, 1] #["root", "dep"] with
  | .error _ => false
  | .ok tree =>
    match Graph.ofTree tree with
    | .error _ => false
    | .ok graph =>
      graph.nodes == #[.word 1, .word 2] && graph.offsets == #[0, 1, 2] &&
        graph.heads == #[.root, .word 1] && graph.relations == #["root", "dep"] &&
        graph.origins == #[.basic, .basic]

#guard treeConversionOk

/- Empty checked trees convert to the valid empty graph. -/
#guard match Tree.ofArrays #[] (#[] : Array String) with
  | .error _ => false
  | .ok tree =>
    match Graph.ofTree tree with
    | .ok graph => graph.nodeCount == 0 && graph.edgeCount == 0
    | .error _ => false

/- Relation mapping preserves node and provenance columns when ordering remains canonical. -/
#guard match Graph.ofRows richRows with
  | .error _ => false
  | .ok graph =>
    match graph.mapRelations (fun relation ↦ relation ++ "!") with
    | .error _ => false
    | .ok mapped => mapped.nodes == graph.nodes && mapped.origins == graph.origins

/- A non-monotone relation map reorders arcs and retains each arc's provenance. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc .root "a" .basic, arc .root "b" .copy]] with
  | .error _ => false
  | .ok graph =>
    match graph.mapRelations fun relation ↦ if relation == "a" then "z" else "a" with
    | .error _ => false
    | .ok mapped =>
      mapped.incoming? (.word 1) ==
        some (row (.word 1) #[arc .root "a" .copy, arc .root "z" .basic])

/- Relation mapping reports collisions that become adjacent only after canonical reordering. -/
#guard match Graph.ofRows
    #[row (.word 1) #[arc .root "a", arc .root "b", arc .root "c"]] with
  | .error _ => false
  | .ok graph =>
    match graph.mapRelations fun relation ↦ if relation == "b" then "z" else "same" with
    | .error (.duplicateArc (.word 1) .root "same") => true
    | _ => false

/-- Read one little-endian bit from the four-edge exhaustive test mask. -/
@[inline] private def edgeBit (mask index : Nat) : Bool :=
  mask / (2 ^ index) % 2 == 1

/-- Compile one of all sixteen simple two-node rooted-graph candidates. -/
private def acceptsMask (mask : Nat) : Bool := Id.run do
  let mut first : Array (Arc String) := #[]
  let mut second : Array (Arc String) := #[]
  if edgeBit mask 0 then first := first.push (arc .root "root")
  if edgeBit mask 1 then first := first.push (arc (.word 2) "edge")
  if edgeBit mask 2 then second := second.push (arc .root "root")
  if edgeBit mask 3 then second := second.push (arc (.word 1) "edge")
  return (Graph.ofRows #[row (.word 1) first, row (.word 2) second]).isOk

/-- Independent validity oracle for one two-node candidate. -/
private def expectedMask (mask : Nat) : Bool :=
  let rootFirst := edgeBit mask 0
  let secondToFirst := edgeBit mask 1
  let rootSecond := edgeBit mask 2
  let firstToSecond := edgeBit mask 3
  let firstIncoming := rootFirst || secondToFirst
  let secondIncoming := rootSecond || firstToSecond
  let firstReachable := rootFirst || (rootSecond && secondToFirst)
  let secondReachable := rootSecond || (rootFirst && firstToSecond)
  firstIncoming && secondIncoming && firstReachable && secondReachable

/- Every simple two-node graph agrees with the independent rooted-reachability oracle. -/
#guard (List.range 16).all fun mask ↦ acceptsMask mask == expectedMask mask

end NlpTests.Core.DependencyGraph
