import Mathlib

namespace PowerMethod

/-- **Spectral decomposition of iterates.** For a self-adjoint operator `T` on a finite-dimensional
inner product space `E`, expanding a vector `x0` in the orthonormal eigenbasis of `T` shows that
the `k`-th iterate `T^k x0` is obtained by raising each eigenvalue coefficient to the `k`-th
power. -/
theorem iterate_eq_sum
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (x0 : E) (k : ℕ) :
    (T ^ k) x0 = ∑ i, ((hT.eigenvectorBasis hn).repr x0 i * (hT.eigenvalues hn i : 𝕜) ^ k) •
      hT.eigenvectorBasis hn i := by
  sorry

end PowerMethod
