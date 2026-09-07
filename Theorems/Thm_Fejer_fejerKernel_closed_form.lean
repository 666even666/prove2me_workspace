import Mathlib
import Definitions.Def_Fejer_fejerKernel

namespace Fejer

/-- **Closed form and nonnegativity of the Fejér kernel.** For every `N` and `θ` not an integer
multiple of `2π`,
`F_N(θ) = (1/(N+1)) · (sin((N+1)θ/2) / sin(θ/2))²`,
and consequently `F_N(θ) ≥ 0` for every `θ` (including the multiples of `2π`, where `F_N(θ) =
N+1` by direct summation). -/
theorem fejerKernel_closed_form
    (N : ℕ) (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ 2 * Real.pi * k) :
    fejerKernel N θ = (1 / (N + 1)) * (Real.sin ((N + 1) * θ / 2) / Real.sin (θ / 2)) ^ 2 := by
  sorry

theorem fejerKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ fejerKernel N θ := by
  sorry

end Fejer
