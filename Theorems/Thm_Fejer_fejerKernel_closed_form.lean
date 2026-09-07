import Mathlib
import Definitions.Def_Fejer_fejerKernel

namespace Fejer

/-- **Closed form of the Fejér kernel.** For every `N` and `θ` not an integer multiple of
`2π`, `F_N(θ) = (1/(N+1)) · (sin((N+1)θ/2) / sin(θ/2))²`. -/
theorem fejerKernel_closed_form
    (N : ℕ) (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ 2 * Real.pi * k) :
    fejerKernel N θ = (1 / (N + 1)) * (Real.sin ((N + 1) * θ / 2) / Real.sin (θ / 2)) ^ 2 := by
  sorry

end Fejer
