import Nlp.Syntax.AnnTree

namespace NlpTests.Syntax.AnnTree

open Nlp

private def sample : AnnTree Nat String :=
  .mk 0 (.node "S" #[.mk 1 (.leaf "dogs"), .mk 2 (.node "VP" #[.mk 3 (.leaf "bark")])])

#guard sample.ann == 0

#guard
    sample.cata (fun annotation word => word ++ toString annotation)
      (fun annotation label children =>
        label ++ toString annotation ++ "(" ++ String.intercalate " " children.toList ++ ")") =
      "S0(dogs1 VP2(bark3))"

end NlpTests.Syntax.AnnTree
