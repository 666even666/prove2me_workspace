import Definitions.Def_DDPM_process
open MeasureTheory Real

namespace DDPM

theorem variational_bound {d : ℕ} (s : Schedule) (T : ℕ)
    (mu : ℕ → Space d → Space d) (v : ℕ → ℝ) (hv : ∀ t, 0 < v t) (x0 : Space d)
    (hp : Integrable fun y : Fin T → Space d => pJoint T mu v (Fin.cons x0 y))
    (hL : Integrable fun y : Fin T → Space d =>
      (-Real.log (pJoint T mu v (Fin.cons x0 y) / qCond s T (Fin.cons x0 y))) *
        qCond s T (Fin.cons x0 y)) :
    -Real.log (pMarginal T mu v x0) ≤ vbCond s T mu v x0 := by sorry

end DDPM
