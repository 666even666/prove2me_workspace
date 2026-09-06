import Mathlib
import Definitions.Def_PositiveDefinite

namespace Bochner

open MeasureTheory

/-- **Bochner's theorem** (Bochner–Herglotz representation theorem). If `f : ℝ → ℂ` is
continuous, positive-definite, and normalized (`f 0 = 1`), then `f` is the Fourier–Stieltjes
transform of a probability measure `ν` on `ℝ`: there exists a probability measure `ν` such that
`f x = ∫ e^{i2πξx} dν(ξ)` for every `x`. No integrability hypothesis on `f` itself is needed
here — this is the general representation theorem, of which the `L¹` case (where `f` is
additionally Lebesgue-integrable, so that `ν` has a continuous density given directly by the
Fourier transform of `f`) is a corollary. -/
theorem bochner_theorem
    (f : ℝ → ℂ) (hf_cont : Continuous f) (hf_pd : IsPositiveDefinite f) (hf0 : f 0 = 1) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ x : ℝ, f x = ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * ξ * x) ∂ν := by
  sorry

end Bochner
