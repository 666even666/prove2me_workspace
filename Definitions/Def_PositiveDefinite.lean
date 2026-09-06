import Mathlib

namespace Bochner

/-- A function `f : ℝ → ℂ` is **positive-definite** if, for every finite family of points
`x_1, …, x_n ∈ ℝ` and complex coefficients `c_1, …, c_n`, the associated Hermitian quadratic
form `∑_{i,j} conj(c_i) c_j f(x_i - x_j)` is real (has zero imaginary part) and nonnegative. -/
def IsPositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * f (x i - x j)).im = 0 ∧
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * f (x i - x j)).re

/-- `f 0` is real: `(f 0).im = 0`. Take `n = 1`, the single point `0`, coefficient `1`. -/
theorem IsPositiveDefinite.zero_im {f : ℝ → ℂ} (hf : IsPositiveDefinite f) : (f 0).im = 0 := by
  have h := (hf 1 ![0] ![1]).1
  simpa using h

/-- `f 0` is nonnegative (and real, by `zero_im`). -/
theorem IsPositiveDefinite.zero_nonneg {f : ℝ → ℂ} (hf : IsPositiveDefinite f) :
    0 ≤ (f 0).re := by
  have h := (hf 1 ![0] ![1]).2
  simpa using h

/-- A positive-definite function is **Hermitian-symmetric**: `f (-x) = conj (f x)`. Take `n = 2`,
points `(0, x)`, and test both `c = (1, 1)` and `c = (1, i)`; the vanishing imaginary part of the
resulting quadratic form in each case pins down, respectively, the real and imaginary parts of
`f (-x) - conj (f x)`. -/
theorem IsPositiveDefinite.conj_neg {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (x : ℝ) :
    f (-x) = starRingEnd ℂ (f x) := by
  have hA : (f 0).im = 0 := hf.zero_im
  have e1 : (2 * f 0 + f (-x) + f x).im = 0 := by
    have h := (hf 2 ![0, x] ![1, 1]).1
    have hsum : (∑ i : Fin 2, ∑ j : Fin 2,
        starRingEnd ℂ (![(1 : ℂ), 1] i) * ![(1 : ℂ), 1] j *
          f (![(0 : ℝ), x] i - ![(0 : ℝ), x] j))
        = 2 * f 0 + f (-x) + f x := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_one, one_mul, sub_self, sub_zero, zero_sub]
      ring
    rwa [hsum] at h
  have e2 : (2 * f 0 + Complex.I * (f (-x) - f x)).im = 0 := by
    have h := (hf 2 ![0, x] ![1, Complex.I]).1
    have hsum : (∑ i : Fin 2, ∑ j : Fin 2,
        starRingEnd ℂ (![(1 : ℂ), Complex.I] i) * ![(1 : ℂ), Complex.I] j *
          f (![(0 : ℝ), x] i - ![(0 : ℝ), x] j))
        = 2 * f 0 + Complex.I * (f (-x) - f x) := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_one, one_mul, sub_self, sub_zero, zero_sub, Complex.conj_I]
      have hII : (-Complex.I) * Complex.I * f 0 = f 0 := by
        rw [neg_mul, Complex.I_mul_I]; ring
      rw [hII]
      ring
    rwa [hsum] at h
  simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.sub_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at e1 e2
  norm_num at e1 e2
  refine Complex.ext ?_ ?_
  · simp only [Complex.conj_re]; nlinarith [e1, e2, hA]
  · simp only [Complex.conj_im]; nlinarith [e1, e2, hA]

/-- The (real part of the) Fourier transform of `f : ℝ → ℂ` at frequency `ξ`:
`∫ f(x) e^{-i2πξx} dx`. -/
noncomputable def fourierTransform (f : ℝ → ℂ) (ξ : ℝ) : ℝ :=
  (∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ξ * x)) * f x).re

end Bochner
