import Mathlib

namespace PowerMethod

/-- **Convergence of the rescaled power iterates.** Let `T` be self-adjoint on a finite-dimensional
inner product space `E`, with eigenvalue `hT.eigenvalues hn i0` strictly dominant in absolute value
over every other eigenvalue, and let `x0` have a nonzero component along the corresponding
eigenvector. Then the iterates `T^k x0`, rescaled by `(eigenvalues i0)^k`, converge to the
projection of `x0` onto the dominant eigenspace. -/
theorem rescaled_iterate_tendsto
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (x0 : E) (i0 : Fin n)
    (hdom : ∀ j, j ≠ i0 → |hT.eigenvalues hn j| < |hT.eigenvalues hn i0|)
    (hne0 : hT.eigenvalues hn i0 ≠ 0)
    (hx0 : (hT.eigenvectorBasis hn).repr x0 i0 ≠ 0) :
    Filter.Tendsto
      (fun k => ((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0)
      Filter.atTop
      (nhds (((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0)) := by
  sorry

end PowerMethod
