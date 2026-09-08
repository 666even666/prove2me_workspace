import Definitions.Def_DDPM_process
open MeasureTheory Real

namespace DDPM

theorem forward_posterior {d : ℕ} (s : Schedule) (t : ℕ) (ht : 2 ≤ t) (x0 xt xprev : Space d) :
    gaussPDF (Real.sqrt (1 - s.beta t) • xprev) (s.beta t) xt * qMarginal s (t - 1) x0 xprev /
        qMarginal s t x0 xt
      = gaussPDF (posteriorMean s t xt x0) (posteriorVar s t) xprev := by sorry

end DDPM
