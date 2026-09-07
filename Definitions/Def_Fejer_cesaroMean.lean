import Mathlib
import Definitions.Def_Fejer_partialSum

namespace Fejer

/-- The `N`-th Cesàro (Fejér) mean of the Fourier series of `f`,
`σ_N(f) = (1/(N+1)) ∑_{n=0}^{N} S_n(f)`. -/
noncomputable def cesaroMean (f : ℝ → ℂ) (N : ℕ) (θ : ℝ) : ℂ :=
  (1 / ((N : ℂ) + 1)) * ∑ n ∈ Finset.range (N + 1), partialSum f n θ

end Fejer
