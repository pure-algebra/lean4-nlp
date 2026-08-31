/-!
# Semiring operations

The runtime-facing algebraic interface contains data only.  Laws live in
`Nlp.Core.Algebra.Laws`, so dynamic-programming kernels can require exactly the operations they
execute.
-/

namespace Nlp

/-- The four operations used by semiring-generic dynamic programs. -/
class SemiringOps (K : Type u) extends Zero K, One K, Add K, Mul K

/-- Kleene star as an optional operation, separate from the four semiring operations. -/
class StarOps (K : Type u) where
  /-- Sum of all finite powers of a value, when the carrier provides it. -/
  star : K → K

export StarOps (star)

/-- Semiring addition.  This is an alias for the carrier's ordinary `Add.add`. -/
@[inline] def oplus {K : Type u} [Add K] (a b : K) : K := a + b

/-- Semiring multiplication.  This is an alias for the carrier's ordinary `Mul.mul`. -/
@[inline] def otimes {K : Type u} [Mul K] (a b : K) : K := a * b

@[inherit_doc] infixl:65 " ⊕ " => oplus
@[inherit_doc] infixl:70 " ⊗ " => otimes
@[inherit_doc] postfix:max "⋆" => StarOps.star

end Nlp
