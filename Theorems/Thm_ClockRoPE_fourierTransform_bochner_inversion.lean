import Mathlib
import Definitions.Def_PositiveDefiniteKernel

namespace ClockRoPE

open MeasureTheory

/-- **Bochner's theorem + Fourier inversion, L¹ case.** If `f : ℝ → ℝ` is continuous,
Lebesgue-integrable, positive-definite, and normalized (`f 0 = 1`), then its Fourier transform
`fourierTransform f` is everywhere nonnegative, integrates to `1`, and recovers `f` by Fourier
inversion. This packages exactly the two classical facts (Bochner's theorem and the Fourier
inversion formula) that Chen et al., *ClockRoPE: Random Fourier Rotations for Temporal Routine
Modeling* (arXiv:2607.26369), combine without proof at the start of the proof of Proposition 3.1
(Eq. 6: `f(p_m-p_n) = ∫ e^{i2πξ(p_m-p_n)} τ(ξ) dξ`), generalized here to hold at every point `x`,
not only at the specific difference `p_m - p_n` the paper needs. -/
theorem fourierTransform_bochner_inversion
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPositiveDefiniteKernel f) (hf0 : f 0 = 1) :
    Continuous (fourierTransform f) ∧
      (∀ ξ : ℝ, 0 ≤ fourierTransform f ξ) ∧
      (∫ ξ : ℝ, fourierTransform f ξ = 1) ∧
      (∀ x : ℝ, (f x : ℂ) =
        ∫ ξ : ℝ, Complex.exp (2 * Real.pi * Complex.I * ξ * x) * (fourierTransform f ξ : ℂ)) := by
  sorry

end ClockRoPE
