import Mathlib
import Definitions.Def_Fejer_fejerKernel

namespace Fejer

open MeasureTheory

/-- **The Fejér kernel has integral `1` over one period.** -/
theorem fejerKernel_integral_eq_one (N : ℕ) :
    (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, fejerKernel N θ = 1 := by
  sorry

end Fejer
