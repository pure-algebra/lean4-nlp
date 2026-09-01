import Nlp.Sequence.PosTaggerLemmas

namespace NlpTests.Sequence.PosTaggerLemmas

open Nlp Nlp.Sequence

/-- Named form encoding has one observation per source token. -/
example (tagger : PosTagger) (forms : Array String) :
    (tagger.encodeForms forms).size = forms.size :=
  Nlp.Sequence.PosTagger.encodeForms_size tagger forms

/-- Validated named decoding has one dense state per source token. -/
example (tagger : PosTagger) (forms : Array String) :
    (tagger.decodeForms forms).size = forms.size :=
  Nlp.Sequence.PosTagger.decodeForms_size tagger forms

/-- Resolving dense states produces a complete POS column. -/
example (tagger : PosTagger) (forms : Array String) :
    (tagger.tagForms forms).size = forms.size :=
  Nlp.Sequence.PosTagger.tagForms_size tagger forms

/-- Exact vocabulary hits retain their compiled numeric observations. -/
example (tagger : PosTagger) (form : String) (word : Tok)
    (found : tagger.words.lookup? form = some word) : tagger.encode form = word :=
  Nlp.Sequence.PosTagger.encode_eq_of_lookup?_eq_some tagger form word found

/-- Missing forms select the reserved OOV observation. -/
example (tagger : PosTagger) (form : String)
    (missing : tagger.words.lookup? form = none) : tagger.encode form = tagger.oov :=
  Nlp.Sequence.PosTagger.encode_eq_oov_of_lookup?_eq_none tagger form missing

/-- The private validated model retains the positive-state premise used by the size theorem. -/
example (tagger : PosTagger) : 0 < tagger.hmm.nTags :=
  tagger.positiveTags

/-- The private validated model retains the HMM's dense-storage invariant. -/
example (tagger : PosTagger) : tagger.hmm.WF :=
  tagger.wellFormedHmm

/-- Every numeric state has one configured output name. -/
example (tagger : PosTagger) : tagger.tagNames.size = tagger.hmm.nTags :=
  tagger.tagCount

end NlpTests.Sequence.PosTaggerLemmas
