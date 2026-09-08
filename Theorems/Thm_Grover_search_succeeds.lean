import Mathlib
import Definitions.Def_groverIterate

namespace Grover

/-- **Grover's algorithm finds the marked item** (Goal). Starting from the uniform superposition
over `N` basis states, some number of applications of the Grover iterate produces a state in which
the probability of measuring the marked index `w0` is at least `1 - 1/N`. -/
theorem search_succeeds {N : ℕ} (w0 : Fin N) :
    ∃ k : ℕ, (1 : ℝ) - 1 / (N : ℝ) ≤
      ‖inner (𝕜 := ℂ) (EuclideanSpace.single w0 (1 : ℂ))
        ((⇑(groverIterate w0))^[k] (uniformSuperposition N))‖ ^ 2 := by
  sorry

end Grover
