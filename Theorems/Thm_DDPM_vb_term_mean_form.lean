import Definitions.Def_DDPM_process
open MeasureTheory Real

namespace DDPM

theorem vb_term_mean_form {d : ℕ} (s : Schedule) (t : ℕ) (ht : 2 ≤ t)
    (mu : ℕ → Space d → Space d) (v : ℕ → ℝ) (hv : 0 < v t) (x0 : Space d)
    (hint : Integrable fun xt : Space d =>
      qMarginal s t x0 xt * ‖posteriorMean s t xt x0 - mu t xt‖ ^ 2) :
    termMid s mu v t x0
      = (∫ xt, qMarginal s t x0 xt * (1 / (2 * v t)) * ‖posteriorMean s t xt x0 - mu t xt‖ ^ 2)
        + (d : ℝ) / 2 * (posteriorVar s t / v t - 1 - Real.log (posteriorVar s t / v t)) := by
  sorry

end DDPM
