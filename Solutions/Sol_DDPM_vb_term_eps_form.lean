import Definitions.Def_DDPM_process
import Theorems.Thm_DDPM_vb_term_mean_form
import Theorems.Thm_DDPM_posterior_mean_eps_form
open MeasureTheory Real ProbabilityTheory WithLp Module
open DDPM

theorem solution {d : ℕ} (s : Schedule) (t : ℕ) (ht : 2 ≤ t)
    (eps : ℕ → Space d → Space d) (heps : Measurable (eps t))
    (v : ℕ → ℝ) (hv : 0 < v t) (x0 : Space d)
    (hint : Integrable fun e : Space d =>
      gaussPDF (0 : Space d) 1 e * ‖e - eps t (noised s t x0 e)‖ ^ 2) :
    termMid s (muEps s eps) v t x0
        - (d : ℝ) / 2 * (posteriorVar s t / v t - 1 - Real.log (posteriorVar s t / v t))
      = ∫ e, gaussPDF (0 : Space d) 1 e *
          (s.beta t ^ 2 / (2 * v t * alpha s t * (1 - alphaBar s t))) *
            ‖e - eps t (noised s t x0 e)‖ ^ 2 := by
  ---- schedule facts
  have hbpos : ∀ m : ℕ, 0 < alphaBar s m := by
    intro m; unfold alphaBar alpha
    exact Finset.prod_pos fun i _ => by linarith [s.beta_lt_one i]
  have hble : ∀ m : ℕ, alphaBar s m ≤ 1 := by
    intro m; unfold alphaBar alpha
    exact Finset.prod_le_one (fun i _ => by linarith [s.beta_lt_one i])
      (fun i _ => by linarith [s.beta_pos i])
  have hblt : ∀ m : ℕ, 1 ≤ m → alphaBar s m < 1 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hsp : alphaBar s (k + 1) = alphaBar s k * alpha s (k + 1) := by
      unfold alphaBar; rw [Finset.prod_Icc_succ_top (by omega)]
    rw [hsp]
    have h1 : 0 < alpha s (k + 1) := by unfold alpha; linarith [s.beta_lt_one (k + 1)]
    have h2 : alpha s (k + 1) < 1 := by unfold alpha; linarith [s.beta_pos (k + 1)]
    nlinarith [hble k, hbpos k]
  have halp : 0 < alpha s t := by unfold alpha; linarith [s.beta_lt_one t]
  have hot : (0:ℝ) < 1 - alphaBar s t := by linarith [hblt t (by omega)]
  have hbt : 0 < alphaBar s t := hbpos t
  ---- opaque square roots
  obtain ⟨g, hgpos, hg2⟩ : ∃ g : ℝ, 0 < g ∧ g ^ 2 = alphaBar s t :=
    ⟨Real.sqrt (alphaBar s t), Real.sqrt_pos.mpr hbt, Real.sq_sqrt hbt.le⟩
  obtain ⟨a, hapos, ha2⟩ : ∃ a : ℝ, 0 < a ∧ a ^ 2 = 1 - alphaBar s t :=
    ⟨Real.sqrt (1 - alphaBar s t), Real.sqrt_pos.mpr hot, Real.sq_sqrt hot.le⟩
  obtain ⟨r, hrpos, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = alpha s t :=
    ⟨Real.sqrt (alpha s t), Real.sqrt_pos.mpr halp, Real.sq_sqrt halp.le⟩
  have hsg : Real.sqrt (alphaBar s t) = g := by rw [← hg2, Real.sqrt_sq hgpos.le]
  have hsa : Real.sqrt (1 - alphaBar s t) = a := by rw [← ha2, Real.sqrt_sq hapos.le]
  have hsr : Real.sqrt (alpha s t) = r := by rw [← hr2, Real.sqrt_sq hrpos.le]
  have hadn : (a : ℝ) ^ d ≠ 0 := pow_ne_zero _ (ne_of_gt hapos)
  set w : ℝ := s.beta t ^ 2 / (2 * v t * alpha s t * (1 - alphaBar s t)) with hw
  ---- the forward sample as an affine map
  have hnoised : ∀ e : Space d, noised s t x0 e = a • e + g • x0 := by
    intro e; unfold noised; rw [hsg, hsa, add_comm]
  ---- change of variables e ↦ a • e + g • x₀
  have hcov : ∀ G : Space d → ℝ,
      ∫ e : Space d, G (a • e + g • x0) = (a ^ d)⁻¹ * ∫ x : Space d, G x := by
    intro G
    have h1 : ∫ e : Space d, G (a • e + g • x0)
        = ∫ e : Space d, (fun y : Space d => G (y + g • x0)) (a • e) := rfl
    rw [h1, MeasureTheory.Measure.integral_comp_smul (volume : Measure (Space d))
      (fun y : Space d => G (y + g • x0)) a, integral_add_right_eq_self,
      finrank_euclideanSpace_fin, smul_eq_mul, abs_of_nonneg (by positivity)]
  have htrans : ∀ F : Space d → ℝ,
      Integrable (fun e : Space d => F (a • e + g • x0)) → Integrable F := by
    intro F hF
    have h1 : Integrable (fun y : Space d => F (y + g • x0)) :=
      (integrable_comp_smul_iff (volume : Measure (Space d))
        (fun y : Space d => F (y + g • x0)) (ne_of_gt hapos)).mp hF
    simpa using h1.comp_sub_right (g • x0)
  ---- the marginal density along that map
  have hdens : ∀ e : Space d,
      qMarginal s t x0 (a • e + g • x0) = (a ^ d)⁻¹ * gaussPDF (0 : Space d) 1 e := by
    intro e
    have hnrm : ‖a • e + g • x0 - g • x0‖ ^ 2 = a ^ 2 * ‖e‖ ^ 2 := by
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [qMarginal, gaussPDF, hsg, hnrm, sub_zero]
    rw [← ha2, Real.mul_rpow (by positivity) (by positivity)]
    have hc : (a ^ 2) ^ (-(d:ℝ) / 2) = ((a : ℝ) ^ d)⁻¹ := by
      rw [← Real.rpow_natCast a 2, ← Real.rpow_natCast a d, ← Real.rpow_mul hapos.le,
        ← Real.rpow_neg hapos.le]
      congr 1
      push_cast
      ring
    rw [hc]
    have hexp : -(a ^ 2 * ‖e‖ ^ 2) / (2 * a ^ 2) = -‖e‖ ^ 2 / (2 * 1) := by
      have : (a:ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hapos)
      field_simp
    rw [hexp]
    ring
  ---- the pointwise identity coming from the ε-parameterization
  have hpt : ∀ e : Space d,
      qMarginal s t x0 (a • e + g • x0) * (1 / (2 * v t))
          * ‖posteriorMean s t (a • e + g • x0) x0 - muEps s eps t (a • e + g • x0)‖ ^ 2
        = (a ^ d)⁻¹ * (gaussPDF (0 : Space d) 1 e
            * (w * ‖e - eps t (noised s t x0 e)‖ ^ 2)) := by
    intro e
    have hback : (1 / Real.sqrt (alphaBar s t)) • ((a • e + g • x0) - a • e) = x0 := by
      rw [hsg, add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hgpos), one_smul]
    have hpm := DDPM.posterior_mean_eps_form s t (by omega) (a • e + g • x0) e
    rw [hsa, hback] at hpm
    rw [hpm, hdens e, hnoised e]
    unfold muEps
    have hsub : (1 / Real.sqrt (alpha s t)) • ((a • e + g • x0) - (s.beta t / a) • e)
        - (1 / Real.sqrt (alpha s t)) • ((a • e + g • x0)
            - (s.beta t / Real.sqrt (1 - alphaBar s t)) • eps t (a • e + g • x0))
        = ((s.beta t / a) / r) • (eps t (a • e + g • x0) - e) := by
      have hinner : (a • e + g • x0 - (s.beta t / a) • e
          - (a • e + g • x0 - (s.beta t / a) • eps t (a • e + g • x0)))
          = (s.beta t / a) • (eps t (a • e + g • x0) - e) := by module
      rw [hsr, hsa, ← smul_sub, hinner, smul_smul]
      congr 1
      field_simp
    rw [hsub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_rev, div_pow, div_pow,
      hw, ← hr2, ← ha2]
    field_simp
  ---- integrability required by the mean form
  have hintM : Integrable fun xt : Space d =>
      qMarginal s t x0 xt * (1 / (2 * v t))
        * ‖posteriorMean s t xt x0 - muEps s eps t xt‖ ^ 2 := by
    refine htrans _ ?_
    have hbase : Integrable fun e : Space d =>
        (a ^ d)⁻¹ * (gaussPDF (0 : Space d) 1 e * (w * ‖e - eps t (noised s t x0 e)‖ ^ 2)) := by
      refine ((hint.const_mul w).const_mul ((a ^ d)⁻¹)).congr ?_
      filter_upwards with e
      ring
    refine hbase.congr ?_
    filter_upwards with e
    exact (hpt e).symm
  have hintM0 : Integrable fun xt : Space d =>
      qMarginal s t x0 xt * ‖posteriorMean s t xt x0 - muEps s eps t xt‖ ^ 2 := by
    refine (hintM.const_mul (2 * v t)).congr ?_
    filter_upwards with xt
    field_simp
  ---- assemble
  have hF : ∫ xt : Space d, qMarginal s t x0 xt * (1 / (2 * v t))
      * ‖posteriorMean s t xt x0 - muEps s eps t xt‖ ^ 2
      = ∫ e : Space d, gaussPDF (0 : Space d) 1 e * w * ‖e - eps t (noised s t x0 e)‖ ^ 2 := by
    have h1 := hcov fun xt : Space d => qMarginal s t x0 xt * (1 / (2 * v t))
      * ‖posteriorMean s t xt x0 - muEps s eps t xt‖ ^ 2
    simp_rw [hpt] at h1
    rw [integral_const_mul] at h1
    have h2 := mul_left_cancel₀ (inv_ne_zero hadn) h1
    rw [← h2]
    refine integral_congr_ae ?_
    filter_upwards with e
    ring
  rw [DDPM.vb_term_mean_form s t ht (muEps s eps) v hv x0 hintM0, add_sub_cancel_right, hF]
