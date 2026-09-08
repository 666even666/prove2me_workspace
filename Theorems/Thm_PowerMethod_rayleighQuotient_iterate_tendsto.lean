import Mathlib
import Definitions.Def_rayleighQuotient

namespace PowerMethod

/-- **The power method converges** (Goal). Let `T` be self-adjoint on a finite-dimensional inner
product space `E`, with eigenvalue `hT.eigenvalues hn i0` strictly dominant in absolute value, and
let the starting vector `x0` have a nonzero component along the corresponding eigenvector. Then the
Rayleigh quotients of the power iterates `T^k x0` converge to the dominant eigenvalue. -/
theorem rayleighQuotient_iterate_tendsto
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (x0 : E) (i0 : Fin n)
    (hdom : ∀ j, j ≠ i0 → |hT.eigenvalues hn j| < |hT.eigenvalues hn i0|)
    (hne0 : hT.eigenvalues hn i0 ≠ 0)
    (hx0 : (hT.eigenvectorBasis hn).repr x0 i0 ≠ 0) :
    Filter.Tendsto (fun k => rayleighQuotient T ((T ^ k) x0)) Filter.atTop
      (nhds (hT.eigenvalues hn i0)) := by
  sorry

end PowerMethod
