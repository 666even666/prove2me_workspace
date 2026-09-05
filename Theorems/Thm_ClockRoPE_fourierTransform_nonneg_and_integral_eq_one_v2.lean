import Mathlib
import Definitions.Def_PositiveDefiniteKernel

namespace ClockRoPE

open MeasureTheory

/-- **Bochner's theorem, L¹ case** (corrected against `IsPositiveDefiniteKernel`, superseding
`ClockRoPE.fourierTransform_nonneg_and_integral_eq_one`, which used the under-hypothesized
`IsPosDefKernel`). If `f : ℝ → ℝ` is continuous, Lebesgue-integrable, positive-definite, and
normalized (`f 0 = 1`), then its Fourier transform `fourierTransform f` is everywhere
nonnegative and integrates to `1`. -/
theorem fourierTransform_nonneg_and_integral_eq_one_v2
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPositiveDefiniteKernel f) (hf0 : f 0 = 1) :
    (∀ ξ : ℝ, 0 ≤ fourierTransform f ξ) ∧ ∫ ξ : ℝ, fourierTransform f ξ = 1 := by
  sorry

end ClockRoPE
