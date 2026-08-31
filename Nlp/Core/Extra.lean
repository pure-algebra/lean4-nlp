import Std.Data.DHashMap

/-!
# Typed extension columns

Core annotations live in fixed columns on `Doc`. Less common extension columns are confined to
one dependent map so their dynamic lookup cost and weaker static guarantees stay explicit.
-/

namespace Nlp

/-- Extension-column keys supported by the standalone kernel. -/
inductive XKey where
  | truecase
  | shape
  | quoteIdx
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- The value type belonging to an extension key. -/
abbrev XKey.Val : XKey → Type
  | .truecase
  | .shape => Array String
  | .quoteIdx => Array Nat

/-- The one dynamically keyed region of a document. -/
abbrev Extra := Std.DHashMap XKey XKey.Val

end Nlp
