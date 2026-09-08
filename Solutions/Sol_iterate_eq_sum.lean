import Mathlib

theorem solution
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (x0 : E) (k : ℕ) :
    (T ^ k) x0 = ∑ i, ((hT.eigenvectorBasis hn).repr x0 i * (hT.eigenvalues hn i : 𝕜) ^ k) •
      hT.eigenvectorBasis hn i := by
  induction k with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, mul_one]
    exact ((hT.eigenvectorBasis hn).sum_repr x0).symm
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT.apply_eigenvectorBasis hn, smul_smul, pow_succ, mul_assoc]
