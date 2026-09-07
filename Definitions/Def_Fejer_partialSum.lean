import Mathlib
import Definitions.Def_Fejer_fourierCoeff

namespace Fejer

/-- The `N`-th (symmetric) partial sum of the Fourier series of `f`,
`S_N(f)(θ) = ∑_{n=-N}^{N} f̂(n) e^{inθ}`. -/
noncomputable def partialSum (f : ℝ → ℂ) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n * Complex.exp ((n : ℂ) * θ * Complex.I)

end Fejer
