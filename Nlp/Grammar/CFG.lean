import Std.Data.HashMap

/-!
# Context-free grammars

The unrestricted grammar in this module is the specification-side representation.  Parsing
engines consume the dedicated CNF representation from `Nlp.Grammar.CNF` instead.
-/

namespace Nlp

/-- An interned nonterminal identifier. -/
abbrev NT := UInt32

/-- An interned terminal/token identifier. -/
abbrev Tok := UInt32

/-- A symbol on the right-hand side of a context-free production. -/
inductive Sym where
  | nt (value : NT)
  | tm (value : Tok)
deriving BEq, Hashable, DecidableEq, Repr, Inhabited

/-- A weighted, unrestricted context-free production. -/
structure Rule (K : Type) where
  lhs : NT
  rhs : Array Sym
  w : K
deriving Repr, Inhabited

/-- A weighted CFG.  No normalization of production weights is assumed. -/
structure CFG (K : Type) where
  prods : Array (Rule K)
  start : NT
  nNT : Nat
deriving Repr, Inhabited

/-- Whether a production has one of the two strict CNF shapes. -/
def Rule.isCNF (rule : Rule K) : Bool :=
  match rule.rhs.toList with
  | [.nt _, .nt _] => true
  | [.tm _] => true
  | _ => false

/-- Every production in the grammar has strict CNF shape. -/
def CFG.IsCNF (grammar : CFG K) : Prop :=
  ∀ rule ∈ grammar.prods, rule.isCNF = true

instance (grammar : CFG K) : Decidable grammar.IsCNF := by
  unfold CFG.IsCNF
  infer_instance

end Nlp
