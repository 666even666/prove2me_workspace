import Mathlib
import Definitions.Def_Fejer_cesaroMean
import Definitions.Def_Fejer_fejerKernel

namespace Fejer

open MeasureTheory

/-- **The Cesàro mean is convolution with the Fejér kernel.** For `f : ℝ → ℂ` continuous and
`2π`-periodic,
`σ_N(f)(θ) = (1/2π) ∫_{-π}^{π} f(θ - φ) F_N(φ) dφ`. -/
theorem cesaroMean_eq_convolution
    (f : ℝ → ℂ) (hf_cont : Continuous f) (hf_per : Function.Periodic f (2 * Real.pi))
    (N : ℕ) (θ : ℝ) :
    cesaroMean f N θ =
      (1 / (2 * Real.pi)) * ∫ φ in (-Real.pi)..Real.pi, f (θ - φ) * (fejerKernel N φ : ℂ) := by
  sorry

end Fejer
