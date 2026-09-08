import Definitions.Def_DDPM_process
import Theorems.Thm_DDPM_kl_isotropic_gaussian
open MeasureTheory Real ProbabilityTheory WithLp
open DDPM

theorem solution {d : ℕ} (s : Schedule) (t : ℕ) (ht : 2 ≤ t)
    (mu : ℕ → Space d → Space d) (v : ℕ → ℝ) (hv : 0 < v t) (x0 : Space d)
    (hint : Integrable fun xt : Space d =>
      qMarginal s t x0 xt * ‖posteriorMean s t xt x0 - mu t xt‖ ^ 2) :
    termMid s mu v t x0
      = (∫ xt, qMarginal s t x0 xt * (1 / (2 * v t)) * ‖posteriorMean s t xt x0 - mu t xt‖ ^ 2)
        + (d : ℝ) / 2 * (posteriorVar s t / v t - 1 - Real.log (posteriorVar s t / v t)) := by
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
  have hot : (0:ℝ) < 1 - alphaBar s t := by linarith [hblt t (by omega)]
  have hon : (0:ℝ) < 1 - alphaBar s (t - 1) := by linarith [hblt (t - 1) (by omega)]
  have hpv : 0 < posteriorVar s t := by
    unfold posteriorVar
    exact mul_pos (div_pos hon hot) (s.beta_pos t)
  ---- the isotropic Gaussian integrates to one and is integrable
  have coord : ∀ x : Space d, ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro x; rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [sq_abs]
  have chg : ∀ g : Space d → ℝ, ∫ x : Space d, g x = ∫ y : Fin d → ℝ, g (toLp 2 y) := fun g =>
    ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding g).symm
  have chgI : ∀ g : Space d → ℝ,
      Integrable (fun y : Fin d → ℝ => g (toLp 2 y)) ↔ Integrable g := fun g =>
    (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  have factor : ∀ (m : Space d) (w : ℝ), 0 < w → ∀ y : Fin d → ℝ,
      gaussPDF m w (toLp 2 y) = ∏ i, gaussianPDFReal (m i) w.toNNReal (y i) := by
    intro m w hw y
    have hwc : ((w.toNNReal : NNReal) : ℝ) = w := Real.coe_toNNReal w hw.le
    have hpos : (0:ℝ) < 2 * π * w := by positivity
    simp only [gaussianPDFReal, hwc, gaussPDF]
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
    congr 1
    · simp only [Finset.card_univ, Fintype.card_fin]
      rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 * π * w) ^ ((1:ℝ)/2)) d,
        ← Real.rpow_mul hpos.le, ← Real.rpow_neg hpos.le]
      congr 1; ring
    · rw [coord, ← Finset.sum_div, ← Finset.sum_neg_distrib]
      congr 1
  have hne : ∀ w : ℝ, 0 < w → w.toNNReal ≠ 0 := by
    intro w hw; rw [ne_eq, Real.toNNReal_eq_zero]; exact not_le.mpr hw
  have normD : ∀ (m : Space d) (w : ℝ), 0 < w → ∫ x : Space d, gaussPDF m w x = 1 := by
    intro m w hw
    rw [chg]
    simp_rw [factor m w hw]
    rw [integral_fintype_prod_volume_eq_prod fun i => gaussianPDFReal (m i) w.toNNReal]
    simp [integral_gaussianPDFReal_eq_one _ (hne w hw)]
  have intD : ∀ (m : Space d) (w : ℝ), 0 < w → Integrable (gaussPDF m w) := by
    intro m w hw
    rw [← chgI]
    simp_rw [factor m w hw, volume_pi]
    exact Integrable.fintype_prod fun i => integrable_gaussianPDFReal (m i) w.toNNReal
  ---- rewrite each inner KL divergence in closed form
  have hkl : ∀ xt : Space d,
      qMarginal s t x0 xt *
          klPDF (gaussPDF (posteriorMean s t xt x0) (posteriorVar s t)) (gaussPDF (mu t xt) (v t))
        = qMarginal s t x0 xt * (1 / (2 * v t)) * ‖posteriorMean s t xt x0 - mu t xt‖ ^ 2
          + ((d : ℝ) / 2 * (posteriorVar s t / v t - 1 - Real.log (posteriorVar s t / v t)))
            * qMarginal s t x0 xt := by
    intro xt
    rw [DDPM.kl_isotropic_gaussian _ _ _ _ hpv hv]
    ring
  ---- integrability of the two pieces
  have hA : Integrable fun xt : Space d =>
      qMarginal s t x0 xt * (1 / (2 * v t)) * ‖posteriorMean s t xt x0 - mu t xt‖ ^ 2 := by
    refine (hint.const_mul (1 / (2 * v t))).congr ?_
    filter_upwards with xt
    ring
  have hB : Integrable fun xt : Space d =>
      ((d : ℝ) / 2 * (posteriorVar s t / v t - 1 - Real.log (posteriorVar s t / v t)))
        * qMarginal s t x0 xt := by
    exact (intD (Real.sqrt (alphaBar s t) • x0) (1 - alphaBar s t) hot).const_mul _
  ---- assemble
  unfold termMid
  simp_rw [hkl]
  have hq1 : ∫ xt : Space d, qMarginal s t x0 xt = 1 :=
    normD (Real.sqrt (alphaBar s t) • x0) (1 - alphaBar s t) hot
  rw [integral_add hA hB, integral_const_mul, hq1]
  ring
