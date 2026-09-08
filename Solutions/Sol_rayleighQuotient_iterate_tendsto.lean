import Mathlib
import Definitions.Def_rayleighQuotient
import Theorems.Thm_PowerMethod_rescaled_iterate_tendsto

open PowerMethod

theorem solution
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (x0 : E) (i0 : Fin n)
    (hdom : ∀ j, j ≠ i0 → |hT.eigenvalues hn j| < |hT.eigenvalues hn i0|)
    (hne0 : hT.eigenvalues hn i0 ≠ 0)
    (hx0 : (hT.eigenvectorBasis hn).repr x0 i0 ≠ 0) :
    Filter.Tendsto (fun k => rayleighQuotient T ((T ^ k) x0)) Filter.atTop
      (nhds (hT.eigenvalues hn i0)) := by
  have hy := rescaled_iterate_tendsto hT hn x0 i0 hdom hne0 hx0
  have hL_ne : (((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0) ≠ 0 := by
    apply smul_ne_zero hx0
    intro h
    have h1 := (hT.eigenvectorBasis hn).norm_eq_one i0
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hscale : ∀ (c : 𝕜) (v : E), c ≠ 0 →
      rayleighQuotient T (c • v) = rayleighQuotient T v := by
    intro c v hc
    have hnum : RCLike.re (inner (𝕜 := 𝕜) (c • v) (T (c • v))) =
        ‖c‖ ^ 2 * RCLike.re (inner (𝕜 := 𝕜) v (T v)) := by
      rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul,
        ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
    have hden : ‖c • v‖ ^ 2 = ‖c‖ ^ 2 * ‖v‖ ^ 2 := by rw [norm_smul, mul_pow]
    show RCLike.re (inner (𝕜 := 𝕜) (c • v) (T (c • v))) / ‖c • v‖ ^ 2 =
      RCLike.re (inner (𝕜 := 𝕜) v (T v)) / ‖v‖ ^ 2
    rw [hnum, hden]
    exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  have hTk : ∀ k, rayleighQuotient T ((T ^ k) x0) =
      rayleighQuotient T (((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0) := by
    intro k
    have hpow_ne : (hT.eigenvalues hn i0 : 𝕜) ^ k ≠ 0 :=
      pow_ne_zero k (by exact_mod_cast hne0)
    have heq : (hT.eigenvalues hn i0 : 𝕜) ^ k •
        (((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0) = (T ^ k) x0 := by
      rw [smul_smul, mul_inv_cancel₀ hpow_ne, one_smul]
    calc rayleighQuotient T ((T ^ k) x0)
        = rayleighQuotient T ((hT.eigenvalues hn i0 : 𝕜) ^ k •
            (((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0)) := by rw [heq]
      _ = rayleighQuotient T (((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0) :=
          hscale _ _ hpow_ne
  have hRL : rayleighQuotient T
      (((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0) =
      hT.eigenvalues hn i0 := by
    rw [hscale _ _ hx0]
    show RCLike.re (inner (𝕜 := 𝕜) (hT.eigenvectorBasis hn i0) (T (hT.eigenvectorBasis hn i0))) /
      ‖hT.eigenvectorBasis hn i0‖ ^ 2 = hT.eigenvalues hn i0
    rw [hT.apply_eigenvectorBasis hn, inner_smul_right, inner_self_eq_norm_sq_to_K,
      (hT.eigenvectorBasis hn).norm_eq_one i0]
    simp
  have hnum_tendsto : Filter.Tendsto (fun k => RCLike.re (inner (𝕜 := 𝕜)
      (((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0)
      (T (((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0))))
      Filter.atTop
      (nhds (RCLike.re (inner (𝕜 := 𝕜)
        (((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0)
        (T (((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0))))) :=
    (RCLike.continuous_re.tendsto _).comp
      (hy.inner ((T.continuous_of_finiteDimensional.tendsto _).comp hy))
  have hden_tendsto : Filter.Tendsto
      (fun k => ‖(((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0)‖ ^ 2)
      Filter.atTop
      (nhds (‖((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0‖ ^ 2)) :=
    (hy.norm).pow 2
  have hquot_tendsto : Filter.Tendsto
      (fun k => rayleighQuotient T (((hT.eigenvalues hn i0 : 𝕜) ^ k)⁻¹ • (T ^ k) x0))
      Filter.atTop
      (nhds (rayleighQuotient T
        (((hT.eigenvectorBasis hn).repr x0 i0) • hT.eigenvectorBasis hn i0))) :=
    hnum_tendsto.div hden_tendsto (pow_ne_zero 2 (norm_ne_zero_iff.mpr hL_ne))
  rw [hRL] at hquot_tendsto
  simpa only [hTk] using hquot_tendsto
