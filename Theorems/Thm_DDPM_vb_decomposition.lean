import Definitions.Def_DDPM_process
open MeasureTheory Real

namespace DDPM

theorem vb_decomposition {d : ℕ} (s : Schedule) (T : ℕ) (hT : 1 ≤ T)
    (mu : ℕ → Space d → Space d) (v : ℕ → ℝ) (hv : ∀ t, 0 < v t) (x0 : Space d)
    (hL : Integrable fun y : Fin T → Space d =>
      (-Real.log (pJoint T mu v (Fin.cons x0 y) / qCond s T (Fin.cons x0 y))) *
        qCond s T (Fin.cons x0 y))
    (hT' : Integrable fun x : Space d =>
      qMarginal s T x0 x * Real.log (qMarginal s T x0 x / gaussPDF (0 : Space d) 1 x))
    (hmid : ∀ t ∈ Finset.Icc 2 T, Integrable fun xt : Space d =>
      qMarginal s t x0 xt *
        klPDF (gaussPDF (posteriorMean s t xt x0) (posteriorVar s t)) (gaussPDF (mu t xt) (v t)))
    (h0 : Integrable fun x1 : Space d =>
      qMarginal s 1 x0 x1 * (-Real.log (gaussPDF (mu 1 x1) (v 1) x0))) :
    vbCond s T mu v x0
      = termT s T x0 + (∑ t ∈ Finset.Icc 2 T, termMid s mu v t x0) + term0 s mu v x0 := by sorry

end DDPM
