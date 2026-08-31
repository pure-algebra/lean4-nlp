import Nlp.Pipeline.Laws

namespace NlpTests.Pipeline.Laws

open Nlp

private def rename (suffix : String) : Arr Id [] [] :=
  fun doc ↦ { doc with text := doc.text ++ suffix }

example (arrow : Arr Id [] []) : Arr.comp arrow (Arr.id Id []) = arrow :=
  Arr.comp_id arrow

example (arrow : Arr Id [] []) : Arr.comp (Arr.id Id []) arrow = arrow :=
  Arr.id_comp arrow

example (first second third : Arr Id [] []) :
    Arr.comp (Arr.comp first second) third = Arr.comp first (Arr.comp second third) :=
  Arr.comp_assoc first second third

example : (Arr.comp (rename " a") (rename " b") (Doc.empty "x")).text = "x a b" := by
  decide

end NlpTests.Pipeline.Laws
