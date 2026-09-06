import Mathlib
import Definitions.Def_PositiveDefiniteKernel

namespace ClockRoPE

open MeasureTheory

/-- **Continuous extension of positive-definiteness.** If `f : ℝ → ℝ` is continuous and
positive-definite, then for every continuous `φ : ℝ → ℂ` and every `a ≤ b`, the double integral
`∫_a^b ∫_a^b conj(φ(x)) φ(y) f(x - y) dx dy` — the continuous analogue of the finite Hermitian
quadratic form that `IsPositiveDefiniteKernel` requires to be real and nonnegative on every
finite point set — is itself real and nonnegative. This extends the finite/discrete
positive-definite condition to continuous test functions by a standard Riemann-sum/density
argument (approximate `φ` by its values on a fine equally-spaced partition and pass to the
limit using uniform continuity of `φ` and `f` on the compact square), and underlies the passage
from Bochner's theorem to Herglotz's theorem for the nonnegativity of the Fourier coefficients
of a periodic positive-definite function, needed for Corollary 3.3. -/
theorem posDef_continuous_extension
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_pd : IsPositiveDefiniteKernel f)
    (a b : ℝ) (φ : ℝ → ℂ) (hφ_cont : Continuous φ) :
    (∫ x in a..b, ∫ y in a..b,
        (starRingEnd ℂ) (φ x) * φ y * (f (x - y) : ℂ)).im = 0 ∧
    0 ≤ (∫ x in a..b, ∫ y in a..b,
        (starRingEnd ℂ) (φ x) * φ y * (f (x - y) : ℂ)).re := by
  sorry

end ClockRoPE
