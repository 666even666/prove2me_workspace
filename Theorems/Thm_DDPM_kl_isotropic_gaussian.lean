import Definitions.Def_DDPM_process

namespace DDPM

open MeasureTheory Real

/-- KL between isotropic Gaussians -/
theorem kl_isotropic_gaussian {d : ℕ} (m1 m2 : Space d) (v1 v2 : ℝ) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    klPDF (gaussPDF m1 v1) (gaussPDF m2 v2)
      = ‖m1 - m2‖ ^ 2 / (2 * v2) + (d : ℝ) / 2 * (v1 / v2 - 1 - Real.log (v1 / v2)) := by sorry

end DDPM
