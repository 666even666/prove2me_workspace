import Mathlib

namespace Fejer

/-- The `n`-th Fourier coefficient of `f : ℝ → ℂ`,
`f̂(n) = (1/2π) ∫_{-π}^{π} f(θ) e^{-inθ} dθ`. -/
noncomputable def fourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, f θ * Complex.exp (-(n : ℂ) * θ * Complex.I)

end Fejer
