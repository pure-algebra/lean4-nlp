import Init.Data.String.Lemmas.Pattern.TakeDrop.String

/-!
# Reversible suffix rewrites

A rewrite denotes one rational string relation: a shared stem followed by a surface suffix on
one side and a lexical suffix on the other.  Swapping the suffixes turns analysis into generation;
the operation is deliberately relational because English inflection is not a function in either
direction.
-/

namespace Nlp.Morphology

/-- Coarse syntactic categories used by the WordNet detachment rules. -/
inductive Pos where
  | noun
  | properNoun
  | verb
  | auxiliary
  | adjective
  | adverb
  | particle
  | other
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

namespace Pos

/-- Interpret Universal Dependencies or Penn Treebank tags at the morphology boundary. -/
def ofTag (tag : String) : Pos :=
  match tag with
  | "NOUN" => .noun
  | "PROPN" | "NNP" | "NNPS" => .properNoun
  | "VERB" => .verb
  | "AUX" | "MD" => .auxiliary
  | "ADJ" => .adjective
  | "ADV" => .adverb
  | "PART" | "RP" => .particle
  | _ =>
    if tag.startsWith "NN" then .noun
    else if tag.startsWith "VB" then .verb
    else if tag.startsWith "JJ" then .adjective
    else if tag.startsWith "RB" then .adverb
    else .other

end Pos

/-- Replace `surfaceSuffix` with `lexicalSuffix` while preserving the preceding stem. -/
structure Rewrite where
  surfaceSuffix : String
  lexicalSuffix : String
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

namespace Rewrite

/-- Reverse an analysis rule into its generation rule. -/
@[inline] def inverse (rule : Rewrite) : Rewrite :=
  ⟨rule.lexicalSuffix, rule.surfaceSuffix⟩

@[simp] theorem inverse_inverse (rule : Rewrite) : rule.inverse.inverse = rule := by
  cases rule
  rfl

end Rewrite

/-- A proof-relevant application of a suffix rewrite to a shared stem. -/
structure Derivation where
  stem : String
  rule : Rewrite
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Derivation

/-- Reconstruct the inflected surface form represented by a derivation. -/
@[inline] def surface (derivation : Derivation) : String :=
  derivation.stem ++ derivation.rule.surfaceSuffix

/-- Reconstruct the lexical form represented by a derivation. -/
@[inline] def lemma (derivation : Derivation) : String :=
  derivation.stem ++ derivation.rule.lexicalSuffix

/-- View the same relation witness in the opposite direction. -/
@[inline] def reverse (derivation : Derivation) : Derivation :=
  ⟨derivation.stem, derivation.rule.inverse⟩

@[simp] theorem reverse_reverse (derivation : Derivation) :
    derivation.reverse.reverse = derivation := by
  cases derivation
  rfl

@[simp] theorem surface_reverse (derivation : Derivation) :
    derivation.reverse.surface = derivation.lemma := by
  rfl

@[simp] theorem lemma_reverse (derivation : Derivation) :
    derivation.reverse.lemma = derivation.surface := by
  rfl

end Derivation

namespace Rewrite

/--
Apply one analysis rule without copying the unmatched prefix until a suffix actually matches.

The returned derivation retains the rule, so callers can generate the original surface form or
audit which detachment produced a candidate lemma.
-/
@[inline] def analyze? (rule : Rewrite) (surface : String) : Option Derivation :=
  match surface.dropSuffix? rule.surfaceSuffix with
  | some stem => some ⟨stem.copy, rule⟩
  | none => none

/-- Every successful suffix analysis reconstructs the exact source surface form. -/
theorem surface_eq_of_analyze?_eq_some (rule : Rewrite) (surface : String)
    (derivation : Derivation) (found : rule.analyze? surface = some derivation) :
    derivation.surface = surface := by
  unfold analyze? at found
  split at found
  · rename_i stem matched
    cases found
    have reconstructed :=
      String.Slice.eq_append_of_dropSuffix?_string_eq_some
        (s := surface.toSlice) (res := stem) matched
    simpa [Derivation.surface] using reconstructed.symm
  · simp at found

/-- Apply the inverse relation and return the result in the original analysis orientation. -/
@[inline] def generate? (rule : Rewrite) (lemma : String) : Option Derivation :=
  (rule.inverse.analyze? lemma).map Derivation.reverse

/-- Every successful generation reconstructs the exact source lemma. -/
theorem lemma_eq_of_generate?_eq_some (rule : Rewrite) (lemma : String)
    (derivation : Derivation) (found : rule.generate? lemma = some derivation) :
    derivation.lemma = lemma := by
  unfold generate? at found
  cases analyzed : rule.inverse.analyze? lemma with
  | none => simp [analyzed] at found
  | some inverseDerivation =>
    simp only [analyzed, Option.map_some, Option.some.injEq] at found
    subst derivation
    simpa using surface_eq_of_analyze?_eq_some rule.inverse lemma inverseDerivation analyzed

end Rewrite

end Nlp.Morphology
