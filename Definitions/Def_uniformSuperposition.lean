import Mathlib

namespace Grover

/-- The uniform superposition `|s⟩ = (1/√N) ∑ᵢ |i⟩` over `N` basis states, the starting state of
Grover's search algorithm. -/
noncomputable def uniformSuperposition (N : ℕ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ))

end Grover
