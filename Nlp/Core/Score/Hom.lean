import Nlp.Core.Score.Cost
import Nlp.Core.Score.LogProb
import Nlp.Core.Score.Prob
import Nlp.Core.Score.Vit

/-! # Maps between score domains -/

namespace Nlp

/-- Map probability mass into log space. -/
@[inline] def Prob.toLogProb (p : Prob) : LogProb := ⟨Float.log p.toFloat⟩

/--
Negate a log-domain Viterbi weight to obtain a min-plus cost.

This is not a homomorphism from `LogProb`: its addition is log-sum-exp rather than maximum.
-/
@[inline] def LogProb.toCostViterbi (x : LogProb) : Cost := ⟨-x.toFloat⟩

/--
View a probability as a Viterbi score.  This deliberately named approximation replaces summation
with maximum and is not a semiring homomorphism.
-/
@[inline] def Prob.viterbiApprox (p : Prob) : Vit := ⟨p.toFloat⟩

end Nlp
