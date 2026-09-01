import Nlp.Pipeline.Ann
import Nlp.Pipeline.Laws
import Nlp.Pipeline.Effects
import Nlp.Pipeline.Runtime
import Nlp.Pipeline.Files
import Nlp.Pipeline.Parallel
import Nlp.Pipeline.Annotate
import Nlp.Pipeline.Tokenize
import Nlp.Pipeline.Morphology
import Nlp.Pipeline.Pos
import Nlp.Pipeline.Corpora
import Nlp.Pipeline.Parse
import Nlp.Pipeline.Viterbi
import Nlp.Pipeline.Evalb

/-!
# Typed pipelines and the user-facing effect API

`Nlp.NLP` is the preferred application boundary for loading corpora and models, cancellation,
bounded parallel work, parsing, and evaluation. Pure functional kernels remain public under
`Nlp.IO`, `Nlp.Parse`, `Nlp.Eval`, and `Nlp.Ann`; `Ann.lift` embeds a pure annotator without
changing its implementation or moving effects into the hot path.
-/
