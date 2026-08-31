import Nlp.IO.Fields

namespace NlpTests.IO.Fields

open Nlp.IO

example : joinFields ["1", "dogs", "_"] = "1\tdogs\t_" := by decide

example : splitFields "1\tdogs\t_" = ["1", "dogs", "_"] := by decide

example : joinFields (splitFields "\ta\t") = "\ta\t" := joinFields_splitFields _

example : splitFields (joinFields ["", "a", "_"]) = ["", "a", "_"] := by
  apply splitFields_joinFields
  · simp
  · simp

/- The nonempty hypothesis is real: these distinct field lists have the same rendering. -/
example : joinFields [] = joinFields [""] := rfl

/- The tab-free hypothesis is real: an embedded tab becomes a field separator. -/
example : splitFields (joinFields ["a\tb"]) = ["a", "b"] := by decide

/- The raw structural layer preserves `_` literally and does not assign it semantics. -/
example : splitFields (joinFields ["_"]) = ["_"] := by
  apply splitFields_joinFields
  · simp
  · simp

example : OptionalField.parse "_" = .missing := rfl

example : OptionalField.render (.present "__" (by decide)) = "__" := rfl

example : OptionalField.present? "_" = .error .reservedUnderscore := rfl

example : OptionalField.present? "value" = .ok (.present "value" (by decide)) := by
  rfl

example (field : OptionalField) : OptionalField.parse (OptionalField.render field) = field :=
  OptionalField.parse_render field

end NlpTests.IO.Fields
