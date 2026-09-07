import Mathlib
import Definitions.Def_Fejer_fejerKernel

namespace Fejer

/-- **Nonnegativity of the Fejér kernel.** `F_N(θ) ≥ 0` for every `N` and every `θ`. -/
theorem fejerKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ fejerKernel N θ := by
  sorry

end Fejer
