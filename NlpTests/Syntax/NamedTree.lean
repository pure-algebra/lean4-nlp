import Nlp.Syntax.NamedTree

namespace NlpTests.Syntax.NamedTree

open Nlp

private def sample : NamedTree :=
  .node "S" (.node "NP" (.leaf "The") #[.leaf "dog"])
    #[.node "VP" (.leaf "barks") #[.leaf "."]]

private def flat : NamedTree :=
  .node "WORDS" (.leaf "one") #[.leaf "two", .leaf "three", .leaf "four"]

private def badRoot : NamedTree :=
  .node "" (.leaf "word") #[]

private def badDescendant : NamedTree :=
  .node "S" (.node "" (.leaf "word") #[]) #[]

#guard sample.width == 4

#guard sample.yieldForms == #["The", "dog", "barks", "."]

#guard sample.yieldFormsInto #["prefix"] ==
  #["prefix", "The", "dog", "barks", "."]

#guard sample.spans == #[("S", 0, 4), ("NP", 0, 2), ("VP", 2, 4)]

#guard sample.spans 7 == #[("S", 7, 11), ("NP", 7, 9), ("VP", 9, 11)]

#guard (sample.spansFrom 7).2 == 11

#guard sample.categoriesNonempty

#guard !badRoot.categoriesNonempty

#guard !badDescendant.categoriesNonempty

#guard (NamedTree.leaf "").categoriesNonempty

#guard flat.yieldForms.size == flat.width

#guard sample == sample

#guard
  sample.cata (fun _ ↦ 1)
    (fun _ first rest ↦ 1 + first + rest.foldl (· + ·) 0) == 7

example : sample.yieldForms.size = sample.width := NamedTree.yieldForms_size sample

example : (sample.yieldFormsInto #["prefix"]).size = 1 + sample.width :=
  NamedTree.yieldFormsInto_size sample #["prefix"]

example : 0 < flat.width := NamedTree.width_pos flat

end NlpTests.Syntax.NamedTree
