import Mathlib
import Definitions.Def_Fejer_fejerKernel

namespace Fejer

open MeasureTheory

/-- **The Fejér kernel's mass away from the origin vanishes.** For every `δ ∈ (0, π)`,
`∫_{δ ≤ |θ| ≤ π} F_N(θ) dθ → 0` as `N → ∞`. -/
theorem fejerKernel_tendsto_zero_away_from_origin
    (δ : ℝ) (hδ0 : 0 < δ) (hδπ : δ < Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∫ θ in (Set.Icc (-Real.pi) Real.pi) ∩ {θ : ℝ | δ ≤ |θ|}, fejerKernel N θ)
      Filter.atTop (nhds 0) := by
  sorry

end Fejer
