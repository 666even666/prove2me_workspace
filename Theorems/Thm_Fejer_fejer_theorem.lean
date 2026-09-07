import Mathlib
import Definitions.Def_Fejer_cesaroMean

namespace Fejer

/-- **Fejér's theorem** (Fejér, *Untersuchungen über Fouriersche Reihen*, Math. Ann. 58 (1904),
51–69). If `f : ℝ → ℂ` is continuous and `2π`-periodic, the Cesàro means of the partial sums of
its Fourier series converge to `f`, uniformly on `ℝ`. -/
theorem fejer_theorem
    (f : ℝ → ℂ) (hf_cont : Continuous f) (hf_per : Function.Periodic f (2 * Real.pi)) :
    TendstoUniformly (fun N θ => cesaroMean f N θ) f Filter.atTop := by
  sorry

end Fejer
