import Mathlib
import Definitions.Def_Fejer_fejerKernel

namespace Fejer

open MeasureTheory

/-- **The Fejér kernel is a good kernel.** Its integral over one period is always `1`, and for
every `δ ∈ (0, π)` the mass outside a `δ`-neighborhood of `0` vanishes as `N → ∞`:
`∫_{δ ≤ |θ| ≤ π} F_N(θ) dθ → 0`. Together with `fejerKernel_nonneg`
(`Fejer.fejerKernel_nonneg`), these are the three defining properties of a good kernel. -/
theorem fejerKernel_integral_eq_one (N : ℕ) :
    (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, fejerKernel N θ = 1 := by
  sorry

theorem fejerKernel_tendsto_zero_away_from_origin
    (δ : ℝ) (hδ0 : 0 < δ) (hδπ : δ < Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∫ θ in (Set.Icc (-Real.pi) Real.pi) ∩ {θ : ℝ | δ ≤ |θ|}, fejerKernel N θ)
      Filter.atTop (nhds 0) := by
  sorry

end Fejer
