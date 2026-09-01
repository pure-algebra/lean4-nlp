import Nlp.Core.Data.UnionFind

namespace NlpTests.Core.UnionFind

open Nlp

#guard (UnionFind.empty 5).size == 5
#guard (UnionFind.empty 5).parent == #[0, 1, 2, 3, 4]

private def joined : Option UnionFind := do
  let first ← (UnionFind.empty 5).union 0 1
  let second ← first.union 1 2
  second.union 3 4

#guard
  match joined >>= fun sets ↦ sets.connected 0 2 with
  | some (true, _) => true
  | _ => false

#guard
  match joined >>= fun sets ↦ sets.connected 0 4 with
  | some (false, _) => true
  | _ => false

#guard (UnionFind.empty 3).find 3 |>.isNone

private def cyclic : UnionFind :=
  { parent := #[1, 0]
    rank := #[0, 0] }

#guard (cyclic.find 0).isNone

private def missingRank : UnionFind :=
  { parent := #[0]
    rank := #[] }

private def extraRank : UnionFind :=
  { parent := #[0, 1]
    rank := #[0, 0, 0] }

#guard (missingRank.union 0 0).isNone
#guard (extraRank.union 0 1).isNone

end NlpTests.Core.UnionFind
