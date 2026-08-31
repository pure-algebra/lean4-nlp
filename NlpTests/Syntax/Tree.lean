import Nlp.Syntax.Tree

namespace NlpTests.Syntax.Tree

open Nlp

private def sample : Tree :=
  .node 0 (.leaf 10) #[.node 1 (.leaf 11) #[.leaf 12], .leaf 13]

#guard sample.width == 4

#guard sample.yieldWords == #[10, 11, 12, 13]

#guard sample.spans == #[(0, 0, 4), (1, 1, 3)]

#guard sample.cata (fun _ => 1) (fun _ first rest => 1 + first + rest.foldl (· + ·) 0) == 6

end NlpTests.Syntax.Tree
