import Mathlib
import Theorems.Thm_PowerMethod_iterate_eq_sum

open PowerMethod

theorem solution
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
  have hrw : ∀ k, ((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0 =
      ∑ i, ((hT.eigenvectorBasis hn).repr x0 i *
        ((hT.eigenvalues hn i / hT.eigenvalues hn i0 : ℝ) : 𝕜) ^ k) •
        hT.eigenvectorBasis hn i := by
    intro k
    rw [iterate_eq_sum hT hn x0 k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    rw [RCLike.ofReal_div, div_pow]
    ring
  simp only [hrw]
  have hlim : (((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0) =
      ∑ i : Fin n, if i = i0 then
        ((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0 else 0 := by
    rw [Finset.sum_ite_eq']
    simp
  rw [hlim]
  apply tendsto_finsetSum
  intro i _
  by_cases hi : i = i0
  · rw [hi, if_pos rfl]
    have hself : (hT.eigenvalues hn i0 / hT.eigenvalues hn i0 : ℝ) = 1 := div_self hne0
    simp only [hself, RCLike.ofReal_one, one_pow, mul_one]
    exact tendsto_const_nhds
  · rw [if_neg hi]
    have hratio : ‖((hT.eigenvalues hn i / hT.eigenvalues hn i0 : ℝ) : 𝕜)‖ < 1 := by
      rw [RCLike.norm_ofReal, abs_div, div_lt_one (abs_pos.mpr hne0)]
      exact hdom i hi
    have htend : Filter.Tendsto
        (fun k => ((hT.eigenvalues hn i / hT.eigenvalues hn i0 : ℝ) : 𝕜) ^ k)
        Filter.atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hratio
    have hmul : Filter.Tendsto
        (fun k => (hT.eigenvectorBasis hn).repr x0 i *
          ((hT.eigenvalues hn i / hT.eigenvalues hn i0 : ℝ) : 𝕜) ^ k)
        Filter.atTop (nhds 0) := by
      simpa using htend.const_mul ((hT.eigenvectorBasis hn).repr x0 i)
    simpa using hmul.smul_const (hT.eigenvectorBasis hn i)
