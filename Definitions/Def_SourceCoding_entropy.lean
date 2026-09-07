import Mathlib

namespace SourceCoding

/-- The Shannon entropy, in base `D`, of a finite probability distribution `p : ι → ℝ`,
`H_D(p) = -∑ i, p i * log_D (p i)`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) (D : ℕ) : ℝ :=
  -∑ i, p i * Real.logb D (p i)

end SourceCoding
