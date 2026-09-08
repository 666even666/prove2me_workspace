import Definitions.Def_DDPM_process

namespace DDPM

open MeasureTheory Real

/-- Eq. (12) -/
theorem vb_term_eps_form {d : ℕ} (s : Schedule) (t : ℕ) (ht : 2 ≤ t)
    (eps : ℕ → Space d → Space d) (heps : Measurable (eps t))
    (v : ℕ → ℝ) (hv : 0 < v t) (x0 : Space d)
    (hint : Integrable fun e : Space d =>
      gaussPDF (0 : Space d) 1 e * ‖e - eps t (noised s t x0 e)‖ ^ 2) :
    termMid s (muEps s eps) v t x0
        - (d : ℝ) / 2 * (posteriorVar s t / v t - 1 - Real.log (posteriorVar s t / v t))
      = ∫ e, gaussPDF (0 : Space d) 1 e *
          (s.beta t ^ 2 / (2 * v t * alpha s t * (1 - alphaBar s t))) *
            ‖e - eps t (noised s t x0 e)‖ ^ 2 := by sorry

end DDPM
