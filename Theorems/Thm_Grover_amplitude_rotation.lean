import Mathlib
import Definitions.Def_groverIterate

namespace Grover

/-- **The geometric picture of Grover's algorithm.** Let `θ = arcsin(1/√N)`. Starting from the
uniform superposition `|s⟩`, the amplitude on the marked basis state `|w0⟩` after `k` applications
of the Grover iterate `G` is exactly `sin((2k+1)θ)`: each iterate of `G` rotates the state by a
further angle `2θ` inside the two-dimensional real subspace spanned by `|w0⟩` and its orthogonal
complement within `span{|s⟩, |w0⟩}`. -/
theorem amplitude_rotation {N : ℕ} (w0 : Fin N) (k : ℕ) :
    inner (𝕜 := ℂ) (EuclideanSpace.single w0 (1 : ℂ))
      ((⇑(groverIterate w0))^[k] (uniformSuperposition N)) =
    (Real.sin ((2 * k + 1) * Real.arcsin (1 / Real.sqrt N)) : ℂ) := by
  sorry

end Grover
