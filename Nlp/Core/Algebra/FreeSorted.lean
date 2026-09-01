/-!
# Free many-sorted term algebras

`Term sig s` is the free ordered term of output sort `s` over a signature whose generators
declare their input and output sorts. `Term.fold` is the unique homomorphism from this syntax
into any algebra for the same signature.
-/

namespace Nlp.FreeSorted

universe u

/-- A many-sorted signature of generators with ordered input sorts. -/
structure Signature (S : Type u) where
  Gen : Type u
  output : Gen → S
  inputs : Gen → List S

mutual
  /-- A well-sorted free term over `sig`. -/
  inductive Term {S : Type u} (sig : Signature S) : S → Type u where
    | op (gen : sig.Gen) (args : Args sig (sig.inputs gen)) : Term sig (sig.output gen)

  /-- An ordered, heterogeneously sorted list of free terms. -/
  inductive Args {S : Type u} (sig : Signature S) : List S → Type u where
    | nil : Args sig []
    | cons {s : S} {ss : List S} : Term sig s → Args sig ss → Args sig (s :: ss)
end

/-- An ordered, heterogeneously sorted list of values in a carrier family. -/
inductive Values {S : Type u} (Carrier : S → Type u) : List S → Type u where
  | nil : Values Carrier []
  | cons {s : S} {ss : List S} : Carrier s → Values Carrier ss →
      Values Carrier (s :: ss)

/-- An interpretation of every generator of `sig` in a sorted carrier family. -/
structure Algebra {S : Type u} (sig : Signature S) where
  Carrier : S → Type u
  op : (gen : sig.Gen) → Values Carrier (sig.inputs gen) → Carrier (sig.output gen)

mutual
  /-- Evaluate a free term in an algebra. -/
  def Term.fold {S : Type u} {sig : Signature S} (alg : Algebra sig) :
      {s : S} → Term sig s → alg.Carrier s
    | _, .op gen args => alg.op gen (Args.fold alg args)

  /-- Evaluate all terms in a sorted argument list. -/
  def Args.fold {S : Type u} {sig : Signature S} (alg : Algebra sig) :
      {ss : List S} → Args sig ss → Values alg.Carrier ss
    | _, .nil => .nil
    | _, .cons term terms => .cons (Term.fold alg term) (Args.fold alg terms)
end

/-- Apply an arbitrary sorted function to every term in an argument list. -/
def Args.map {S : Type u} {sig : Signature S} {Carrier : S → Type u}
    (f : {s : S} → Term sig s → Carrier s) :
    {ss : List S} → Args sig ss → Values Carrier ss
  | _, .nil => .nil
  | _, .cons term terms => .cons (f term) (Args.map f terms)

/-- Mapping `fold` over arguments is their mutual fold. -/
theorem Args.map_fold {S : Type u} {sig : Signature S} (alg : Algebra sig) :
    {ss : List S} → (args : Args sig ss) →
      Args.map (Term.fold alg) args = Args.fold alg args
  | _, .nil => rfl
  | _, .cons _ terms => by
      simp only [Args.map, Args.fold]
      rw [Args.map_fold alg terms]

/-- A homomorphism from the free term algebra into `alg`. -/
structure Hom {S : Type u} (sig : Signature S) (alg : Algebra sig) where
  toFun : {s : S} → Term sig s → alg.Carrier s
  map_op : ∀ (gen : sig.Gen) (args : Args sig (sig.inputs gen)),
    toFun (.op gen args) = alg.op gen (Args.map toFun args)

instance {S : Type u} {sig : Signature S} {alg : Algebra sig} :
    CoeFun (Hom sig alg) (fun _ ↦ {s : S} → Term sig s → alg.Carrier s) :=
  ⟨Hom.toFun⟩

/-- `Term.fold` packaged as the canonical homomorphism into `alg`. -/
def foldHom {S : Type u} {sig : Signature S} (alg : Algebra sig) : Hom sig alg where
  toFun := Term.fold alg
  map_op gen args := congrArg (alg.op gen) (Args.map_fold alg args).symm

mutual
  /-- Every homomorphism from free terms agrees pointwise with `Term.fold`. -/
  theorem Hom.eq_fold {S : Type u} {sig : Signature S} {alg : Algebra sig}
      (hom : Hom sig alg) {s : S} (term : Term sig s) :
      hom term = Term.fold alg term := by
    cases term with
    | op gen args =>
        rw [hom.map_op]
        exact congrArg (alg.op gen) (Args.map_eq_fold hom args)

  /-- The argument-list half of `Hom.eq_fold`. -/
  theorem Args.map_eq_fold {S : Type u} {sig : Signature S} {alg : Algebra sig}
      (hom : Hom sig alg) {ss : List S} (args : Args sig ss) :
      Args.map hom.toFun args = Args.fold alg args := by
    cases args with
    | nil => rfl
    | cons term terms =>
        simp only [Args.map, Args.fold]
        rw [Hom.eq_fold hom term, Args.map_eq_fold hom terms]
end

end Nlp.FreeSorted
