import Mathlib
import Definitions.Def_groverIterate

namespace Grover

/-- **The Grover iterate is an isometry.** Since both the oracle and the diffusion operator are
reflections, their composition `G` preserves the norm of every state, so Grover's algorithm is a
valid sequence of quantum operations (it maps unit vectors to unit vectors). -/
theorem iterate_isometry {N : ℕ} (w0 : Fin N) (x : EuclideanSpace ℂ (Fin N)) :
    ‖(groverIterate w0) x‖ = ‖x‖ := by
  sorry

end Grover
