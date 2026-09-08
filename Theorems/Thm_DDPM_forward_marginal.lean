import Definitions.Def_DDPM_process

namespace DDPM

open MeasureTheory Real

/-- Eq. (4) -/
theorem forward_marginal {d : ℕ} (s : Schedule) (t : ℕ) (ht : 1 ≤ t) (x0 x : Space d) :
    qFwd s x0 t x = qMarginal s t x0 x := by sorry

end DDPM
