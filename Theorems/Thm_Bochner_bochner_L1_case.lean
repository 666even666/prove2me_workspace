import Mathlib
import Definitions.Def_PositiveDefinite

namespace Bochner

open MeasureTheory

/-- **Bochner's theorem, `L¹` case.** If `f : ℝ → ℝ` is continuous, Lebesgue-integrable,
positive-definite, and normalized (`f 0 = 1`), then its Fourier transform `fourierTransform f`
is everywhere nonnegative, integrates to `1`, and recovers `f` by Fourier inversion. Together
these say the Fourier transform of `f` is (the density of) a probability measure, and `f` is
recovered from it — the density special case of the general representation theorem
(`bochner_theorem`), where the representing measure is absolutely continuous. -/
theorem bochner_L1_case
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPositiveDefinite f) (hf0 : f 0 = 1) :
    Continuous (fourierTransform f) ∧
      (∀ ξ : ℝ, 0 ≤ fourierTransform f ξ) ∧
      (∫ ξ : ℝ, fourierTransform f ξ = 1) ∧
      (∀ x : ℝ, (f x : ℂ) =
        ∫ ξ : ℝ, Complex.exp (2 * Real.pi * Complex.I * ξ * x) * (fourierTransform f ξ : ℂ)) := by
  sorry

end Bochner
