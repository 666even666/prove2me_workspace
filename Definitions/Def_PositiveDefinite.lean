import Mathlib

namespace Bochner

/-- A real-valued function `f : ℝ → ℝ` is **positive-definite** if, for every finite family of
points `x_1, …, x_n ∈ ℝ` and complex coefficients `c_1, …, c_n`, the associated Hermitian
quadratic form `∑_{i,j} conj(c_i) c_j f(x_i - x_j)` is real (has zero imaginary part) and
nonnegative. -/
def IsPositiveDefinite (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * (f (x i - x j) : ℂ)).im = 0 ∧
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * (f (x i - x j) : ℂ)).re

/-- A positive-definite function is even: `f (-x) = f x`. Take `n = 2`, points `(0, x)`, and
coefficients `(1, i)`; the vanishing imaginary part of the resulting quadratic form forces
`f (-x) = f x`. -/
theorem IsPositiveDefinite.even {f : ℝ → ℝ} (hf : IsPositiveDefinite f) (x : ℝ) :
    f (-x) = f x := by
  have h := (hf 2 ![0, x] ![1, Complex.I]).1
  simp [Fin.sum_univ_two, sub_eq_add_neg] at h
  linarith [h]

/-- The (real part of the) Fourier transform of `f : ℝ → ℝ` at frequency `ξ`:
`∫ f(x) e^{-i2πξx} dx`. -/
noncomputable def fourierTransform (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ξ * x)) * (f x : ℂ)).re

end Bochner
