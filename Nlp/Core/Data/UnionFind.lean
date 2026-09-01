/-!
# Persistent union-find

The arrays are updated with Lean's single-owner functional-update discipline. Every lookup is
checked, and `find` is fuel-bounded by the number of nodes, so malformed parent cycles return
`none` rather than introducing partial recursion.
-/

namespace Nlp

/-- A disjoint-set forest with union-by-rank metadata. -/
structure UnionFind where
  parent : Array Nat
  rank : Array Nat
deriving Inhabited, Repr

namespace UnionFind

/-- Number of elements represented by the forest. -/
@[inline] def size (sets : UnionFind) : Nat := sets.parent.size

/-- The cheap structural invariant required by the operations. -/
def WF (sets : UnionFind) : Prop :=
  sets.rank.size = sets.size ∧
    ∀ (i : Nat) (inBounds : i < sets.size), sets.parent[i]'inBounds < sets.size

/-- Create `n` singleton sets. -/
def empty (n : Nat) : UnionFind :=
  { parent := Array.range n
    rank := Array.replicate n 0 }

/-- Follow parents and compress the visited path, using `fuel` as a corruption guard. -/
def findGo : Nat → UnionFind → Nat → Option (Nat × UnionFind)
  | 0, _, _ => none
  | fuel + 1, sets, item =>
      match sets.parent[item]? with
      | none => none
      | some next =>
          if next == item then
            some (item, sets)
          else
            match findGo fuel sets next with
            | none => none
            | some (root, compressed) =>
                match compressed.parent[item]? with
                | none => none
                | some _ =>
                    some (root, { compressed with parent := compressed.parent.set! item root })

/-- Find an element's root and return the path-compressed forest. -/
def find (sets : UnionFind) (item : Nat) : Option (Nat × UnionFind) :=
  findGo (sets.size + 1) sets item

/-- Join two sets with union by rank, returning `none` for malformed or out-of-range input. -/
def union (sets : UnionFind) (left right : Nat) : Option UnionFind :=
  if sets.rank.size != sets.size then
    none
  else do
    let (leftRoot, afterLeft) ← sets.find left
    let (rightRoot, compressed) ← afterLeft.find right
    if leftRoot == rightRoot then
      return compressed
    let leftRank ← compressed.rank[leftRoot]?
    let rightRank ← compressed.rank[rightRoot]?
    if leftRank < rightRank then
      return { compressed with parent := compressed.parent.set! leftRoot rightRoot }
    else if rightRank < leftRank then
      return { compressed with parent := compressed.parent.set! rightRoot leftRoot }
    else
      return { parent := compressed.parent.set! rightRoot leftRoot
               rank := compressed.rank.set! leftRoot (leftRank + 1) }

/-- Decide connectivity and return the path-compressed forest. -/
def connected (sets : UnionFind) (left right : Nat) : Option (Bool × UnionFind) := do
  let (leftRoot, afterLeft) ← sets.find left
  let (rightRoot, compressed) ← afterLeft.find right
  return (leftRoot == rightRoot, compressed)

end UnionFind
end Nlp
