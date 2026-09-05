import Mathlib

namespace ClockRoPE

/-- A real-valued kernel `f : ℝ → ℝ` is *positive definite* if, for every finite family of
points `x : Fin n → ℝ` and complex coefficients `c : Fin n → ℂ`, the Hermitian quadratic form
`∑ i, ∑ j, conj (c i) * c j * f (x i - x j)` has nonnegative real part. This is the standard
positive-definiteness hypothesis of Bochner's theorem. -/
def IsPosDefKernel (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
          starRingEnd ℂ (c i) * c j * (f (x i - x j) : ℂ)).re

/-- The Fourier transform `τ(ξ) = ∫_ℝ f(x) e^{-i2πξx} dx` of a real kernel `f`, taken as a real
number via its real part. For a continuous, Lebesgue-integrable, positive-definite kernel with
`f 0 = 1`, this coincides with the (real-valued) probability density furnished by Bochner's
theorem. -/
noncomputable def fourierTransform (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ξ * x)) * (f x : ℂ)).re

end ClockRoPE
