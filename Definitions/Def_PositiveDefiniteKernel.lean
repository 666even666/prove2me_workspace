import Mathlib

namespace ClockRoPE

/-- A real-valued kernel `f : ℝ → ℝ` is *positive definite* if, for every finite family of
points `x : Fin n → ℝ` and complex coefficients `c : Fin n → ℂ`, the Hermitian quadratic form
`∑ i, ∑ j, conj (c i) * c j * f (x i - x j)` is a real number and is nonnegative. Requiring the
sum to be real (not merely its real part) is the standard positive-definiteness hypothesis of
Bochner's theorem; it is what forces a positive-definite kernel to be even
(`f (-x) = f x`, see `IsPositiveDefiniteKernel.even`), which the Fourier-inversion argument for
Propositions 3.1/3.2 depends on. This supersedes `ClockRoPE.IsPosDefKernel`
(`Definitions.Def_PosDefKernel`), which only constrained the real part and is too weak to force
evenness. -/
def IsPositiveDefiniteKernel (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * (f (x i - x j) : ℂ)).im = 0 ∧
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * (f (x i - x j) : ℂ)).re

/-- A positive-definite real kernel is even: `f (-x) = f x` for every `x`. -/
theorem IsPositiveDefiniteKernel.even {f : ℝ → ℝ} (hf : IsPositiveDefiniteKernel f) (x : ℝ) :
    f (-x) = f x := by
  have h := (hf 2 ![0, x] ![1, Complex.I]).1
  simp [Fin.sum_univ_two, sub_eq_add_neg] at h
  linarith [h]

/-- The Fourier transform `τ(ξ) = ∫_ℝ f(x) e^{-i2πξx} dx` of a real kernel `f`, taken as a real
number via its real part. For a continuous, Lebesgue-integrable, positive-definite kernel with
`f 0 = 1`, this coincides with the (real-valued) probability density furnished by Bochner's
theorem. -/
noncomputable def fourierTransform (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ξ * x)) * (f x : ℂ)).re

end ClockRoPE
