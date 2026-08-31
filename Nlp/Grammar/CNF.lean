import Nlp.Grammar.CFG

/-!
# Chomsky-normal-form grammars

Unlike `Nlp.CFG`, this is an implementation representation: non-CNF productions are
unrepresentable, so the parser does not inspect right-hand-side arrays in its inner loop.
-/

namespace Nlp

/-- A weighted binary production `lhs → rhsLeft rhsRight`. -/
structure BinRule (K : Type) where
  lhs : NT
  r1 : NT
  r2 : NT
  w : K
deriving Repr, Inhabited

/-- A weighted lexical production `lhs → tok`. -/
structure LexRule (K : Type) where
  lhs : NT
  tok : Tok
  w : K
deriving Repr, Inhabited

/-- A grammar whose productions have strict CNF shape by construction. -/
structure CNF (K : Type) where
  bin : Array (BinRule K)
  lex : Array (LexRule K)
  start : NT
  nNT : Nat
deriving Repr, Inhabited

/-- Forget the implementation representation and recover a specification-side CFG. -/
def CNF.toCFG (grammar : CNF K) : CFG K :=
  { prods :=
      grammar.bin.map (fun rule =>
        ⟨rule.lhs, #[.nt rule.r1, .nt rule.r2], rule.w⟩) ++
      grammar.lex.map (fun rule => ⟨rule.lhs, #[.tm rule.tok], rule.w⟩)
    start := grammar.start
    nNT := grammar.nNT }

/-- Forgetting a `CNF` grammar always produces a CFG satisfying `CFG.IsCNF`. -/
theorem CNF.toCFG_isCNF (grammar : CNF K) : grammar.toCFG.IsCNF := by
  intro rule hRule
  simp [CNF.toCFG] at hRule
  rcases hRule with ⟨source, _, rfl⟩ | ⟨source, _, rfl⟩ <;> rfl

end Nlp
