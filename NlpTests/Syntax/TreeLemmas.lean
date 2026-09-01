import Nlp.Syntax.TreeLemmas

namespace NlpTests.Syntax.TreeLemmas

open Nlp

private def sample : Tree :=
  .node 0 (.leaf 10) #[.node 1 (.leaf 11) #[.leaf 12], .leaf 13]

private def deep : Tree :=
  .node 0 (.node 1 (.leaf 10) #[.leaf 11, .node 2 (.leaf 12) #[]])
    #[.leaf 13, .node 3 (.leaf 14) #[.leaf 15]]

-- `yieldWords_size` on concrete trees
#guard sample.yieldWords.size == sample.width
#guard deep.yieldWords.size == deep.width

-- `spansFrom_snd` on concrete trees and fenceposts
#guard (sample.spansFrom 0).2 == 0 + sample.width
#guard (deep.spansFrom 0).2 == 0 + deep.width
#guard (deep.spansFrom 7).2 == 7 + deep.width

-- `width_pos` on concrete trees
#guard 0 < sample.width
#guard 0 < deep.width

-- unfold lemmas agree with the attach-based definitions
#guard deep.width
    == (match deep with
        | .leaf _ => 1
        | .node _ child children =>
            children.foldl (fun total t => total + t.width) child.width)

example : (sample.spansFrom 3).2 = 3 + sample.width := by native_decide
example : deep.yieldWords.size = deep.width := by native_decide
example : 0 < deep.width := by native_decide

-- `spans_mem_bounds` instances: all recorded spans sit inside `[start, start + width]`
example :
    (deep.spans 5).all fun s => 5 ≤ s.2.1 && s.2.1 < s.2.2 && s.2.2 ≤ 5 + deep.width := by
  native_decide

example :
    (sample.spans 0).all fun s => s.2.1 < s.2.2 && s.2.2 ≤ sample.width := by
  native_decide

end NlpTests.Syntax.TreeLemmas
