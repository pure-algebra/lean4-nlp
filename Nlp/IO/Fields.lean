/-!
# Delimiter-safe fields

This module is the syntactic field layer used by tabular corpus formats. It treats tab as the only
structural delimiter and performs no escaping. Consequently, split-after-join is proved only for
nonempty tab-free fields; join-after-split is valid for every raw line.

The literal underscore belongs to the later semantic layer: formats such as CoNLL-U reserve `_`
for a missing value and provide no escape for a present literal underscore. `OptionalField` makes
that limitation explicit instead of claiming an impossible semantic round trip.
-/

namespace Nlp.IO

/-- Join fields with a literal tab. This function does not escape tabs within a field. -/
def joinFields (fields : List String) : String :=
  String.ofList (['\t'].intercalate (fields.map String.toList))

/-- Split a raw line on literal tabs, retaining empty fields. -/
def splitFields (line : String) : List String :=
  (line.toList.splitOn '\t').map String.ofList

/-- Joining the result of splitting reconstructs every raw line. -/
theorem joinFields_splitFields (line : String) : joinFields (splitFields line) = line := by
  simp [joinFields, splitFields, List.intercalate_splitOn]

/-- Splitting a joined, nonempty list of tab-free fields reconstructs the fields exactly.

The two hypotheses are necessary: tabs are delimiters rather than escaped data, and both `[]` and
`[""]` join to the empty string.
-/
theorem splitFields_joinFields (fields : List String)
    (tabFree : ∀ field ∈ fields, '\t' ∉ field.toList) (nonempty : fields ≠ []) :
    splitFields (joinFields fields) = fields := by
  unfold splitFields joinFields
  rw [String.toList_ofList]
  rw [List.splitOn_intercalate (ls := fields.map String.toList) '\t' ?separator ?fields]
  · simp
  · intro chars present
    obtain ⟨field, member, rfl⟩ := List.mem_map.mp present
    exact tabFree field member
  · simpa using nonempty

/-- A semantic optional field for formats that reserve `_` as the sole missing marker.

There is intentionally no `present "_"`: the standard format has no escape that could distinguish
it from `missing`.
-/
inductive OptionalField where
  | missing
  | present (value : String) (notReserved : value ≠ "_")
  deriving Repr, DecidableEq, Inhabited

namespace OptionalField

/-- A caller tried to encode the reserved underscore as a present value. -/
inductive Error where
  | reservedUnderscore
  deriving Repr, DecidableEq, Inhabited

/-- Interpret the reserved underscore as missing and every other raw field as present. -/
def parse (raw : String) : OptionalField :=
  if reserved : raw = "_" then .missing else .present raw reserved

/-- Render a semantic optional field using `_` as the missing marker. -/
def render : OptionalField → String
  | .missing => "_"
  | .present value _ => value

/-- Validate a value intended to be present, rejecting the unescapable literal underscore. -/
def present? (value : String) : Except Error OptionalField :=
  if reserved : value = "_" then .error .reservedUnderscore else .ok (.present value reserved)

theorem render_parse (raw : String) : render (parse raw) = raw := by
  by_cases reserved : raw = "_" <;> simp [parse, render, reserved]

theorem parse_render (field : OptionalField) : parse (render field) = field := by
  cases field with
  | missing => simp [parse, render]
  | present value notReserved => simp [parse, render, notReserved]

end OptionalField

end Nlp.IO
