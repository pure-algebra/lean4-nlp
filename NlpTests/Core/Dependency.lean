import Nlp.Core.Data.Dependency

/-! # Dependency-tree foundation tests -/

namespace NlpTests.Core.Dependency

open Nlp.Dependency

/-- Whether the sentence-tree checker succeeds. -/
private def treeOk (heads : Array Nat) : Bool :=
  match checkSentenceTree heads with
  | .ok () => true
  | .error _ => false

/-- Whether the sentence-tree checker returns one exact typed failure. -/
private def treeErrorIs (heads : Array Nat) (expected : TreeError) : Bool :=
  match checkSentenceTree heads with
  | .ok () => false
  | .error cause => cause == expected

/-- Whether the projectivity checker succeeds. -/
private def projectiveOk (heads : Array Nat) : Bool :=
  match checkProjective heads with
  | .ok () => true
  | .error _ => false

/-- Whether the projectivity checker returns one exact typed failure. -/
private def projectivityErrorIs (heads : Array Nat)
    (expected : ProjectivityError) : Bool :=
  match checkProjective heads with
  | .ok () => false
  | .error cause => cause == expected

/- Empty head columns form the empty dependency tree. -/
#guard treeOk #[]

/- A single word attached to root is a valid projective tree. -/
#guard projectiveOk #[0]

/- Heads may name the final word of the sentence. -/
#guard treeOk #[2, 0]

/- Out-of-range heads retain the 1-based dependent and sentence size. -/
#guard treeErrorIs #[0, 3] (.headOutOfRange 2 3 2)

/- Self heads are rejected at their 1-based dependent position. -/
#guard treeErrorIs #[1] (.selfHead 1)

/- A nonempty functional graph without a root is rejected before cycle analysis. -/
#guard treeErrorIs #[2, 1] .noRoot

/- The second root dependent identifies both root positions. -/
#guard treeErrorIs #[0, 0] (.multipleRoots 1 2)

/- A disconnected two-cycle is reported by the edge that first closes it. -/
#guard treeErrorIs #[0, 3, 2] (.cycle 3 2)

/-- Checked construction requires one relation per dependent. -/
example : (Tree.ofArrays #[0] #["root"]).toOption.map (fun tree ↦ tree.relations) =
    some #["root"] := by
  native_decide

/- Relation-count failures retain expected and observed sizes. -/
#guard match Tree.ofArrays #[0] (#[] : Array String) with
  | .error (.relationCount 1 0) => true
  | _ => false

/-- Mapping relations preserves aligned heads. -/
example :
    (Tree.ofArrays #[2, 0] #["dep", "root"]).toOption.map
      (fun tree ↦ (tree.mapRelations String.length).heads) = some #[2, 0] := by
  native_decide

/- A nested dependency tree is projective. -/
#guard projectiveOk #[2, 0, 2]

/- Crossing arcs do not invalidate the underlying general dependency tree. -/
#guard treeOk #[3, 4, 0, 3]

/- Projectivity reports the first crossing pair without treating it as a malformed tree. -/
#guard projectivityErrorIs #[3, 4, 0, 3] (.crossing 1 3 2 4)

/- Flattened documents validate each sentence in sentence-local coordinates. -/
#guard (checkDocumentTrees #[0, 1, 2, 0] #[2, 4]).isOk

/- A local failure retains its sentence ordinal and flattened half-open range. -/
#guard match checkDocumentTrees #[0, 1, 2, 1] #[2, 4] with
  | .error (.sentence 1 2 4 .noRoot) => true
  | _ => false

/- Sentence ends must cover every flattened head exactly once. -/
#guard match checkDocumentTrees #[0, 1] #[1] with
  | .error (.invalidSentenceEnds 2 #[1]) => true
  | _ => false

/- Empty flattened documents have no sentence boundary. -/
#guard (checkDocumentTrees #[] #[]).isOk

/-- The executable checker characterizations are directly usable as theorems. -/
example (heads : Array Nat) :
    checkSentenceTree heads = .ok () ↔ SentenceTreeWF heads :=
  checkSentenceTree_eq_ok_iff heads

/-- Projectivity has the corresponding checker characterization. -/
example (heads : Array Nat) : checkProjective heads = .ok () ↔ Projective heads :=
  checkProjective_eq_ok_iff heads

/-- Flattened sentence-local trees have the corresponding checker characterization. -/
example (heads ends : Array Nat) :
    checkDocumentTrees heads ends = .ok () ↔ DocumentTreeWF heads ends :=
  checkDocumentTrees_eq_ok_iff heads ends

end NlpTests.Core.Dependency
