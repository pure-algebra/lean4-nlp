import Nlp.Sequence.PosTagger

/-!
# Structural contracts for named HMM part-of-speech tagging

These lemmas expose the column-size and exact-lookup guarantees used by document adapters without
putting proof work in the numeric decoding hot path.
-/

namespace Nlp.Sequence.PosTagger

/-- Encoding preserves the number of input forms. -/
@[simp] theorem encodeForms_size (tagger : PosTagger) (forms : Array String) :
    (tagger.encodeForms forms).size = forms.size := by
  simp [encodeForms]

/-- A compiled vocabulary hit is returned unchanged. -/
theorem encode_eq_of_lookup?_eq_some (tagger : PosTagger) (form : String) (word : Tok)
    (found : tagger.words.lookup? form = some word) : tagger.encode form = word := by
  simp [encode, found]

/-- A form absent from the compiled vocabulary receives the reserved OOV observation. -/
theorem encode_eq_oov_of_lookup?_eq_none (tagger : PosTagger) (form : String)
    (missing : tagger.words.lookup? form = none) : tagger.encode form = tagger.oov := by
  simp [encode, missing]

/-- The validated positive tag count makes named numeric decoding length preserving. -/
@[simp] theorem decodeForms_size (tagger : PosTagger) (forms : Array String) :
    (tagger.decodeForms forms).size = forms.size := by
  rw [decodeForms, Hmm.decode_size]
  split <;> simp_all [encodeForms, Nat.ne_of_gt tagger.positiveTags]

/-- Resolving decoded states to names preserves the complete form-column length. -/
@[simp] theorem tagForms_size (tagger : PosTagger) (forms : Array String) :
    (tagger.tagForms forms).size = forms.size := by
  simp [tagForms]

/-- Empty form input has no numeric tags. -/
@[simp] theorem decodeForms_empty (tagger : PosTagger) : tagger.decodeForms #[] = #[] := by
  simp [decodeForms, encodeForms]

/-- Empty form input has no named tags. -/
@[simp] theorem tagForms_empty (tagger : PosTagger) : tagger.tagForms #[] = #[] := by
  simp [tagForms]

/-- Named decoding resolves a position from the numeric decoder with the configured total lookup. -/
theorem tagForms_getElem (tagger : PosTagger) (forms : Array String) (index : Nat)
    (inBounds : index < forms.size) :
    (tagger.tagForms forms)[index]'(by simpa) =
      tagger.tagNames.getD ((tagger.decodeForms forms)[index]'(by simpa)) "" := by
  simp [tagForms]

end Nlp.Sequence.PosTagger
