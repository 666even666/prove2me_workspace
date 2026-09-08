import Definitions.Def_DDPM_process
open MeasureTheory Real

namespace DDPM

theorem posterior_mean_eps_form {d : ℕ} (s : Schedule) (t : ℕ) (ht : 1 ≤ t) (xt e : Space d) :
    posteriorMean s t xt ((1 / Real.sqrt (alphaBar s t)) • (xt - Real.sqrt (1 - alphaBar s t) • e))
      = (1 / Real.sqrt (alpha s t)) • (xt - (s.beta t / Real.sqrt (1 - alphaBar s t)) • e) := by
  sorry

end DDPM
