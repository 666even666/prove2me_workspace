import Definitions.Def_DDPM_process
open MeasureTheory Real ProbabilityTheory WithLp
open DDPM

theorem solution {d : ℕ} (s : Schedule) (t : ℕ) (ht : 1 ≤ t) (x0 x : Space d) :
    qFwd s x0 t x = qMarginal s t x0 x := by
  ---- schedule facts
  have hbpos : ∀ m : ℕ, 0 < alphaBar s m := by
    intro m; unfold alphaBar alpha
    exact Finset.prod_pos fun i _ => by linarith [s.beta_lt_one i]
  have hble : ∀ m : ℕ, alphaBar s m ≤ 1 := by
    intro m; unfold alphaBar alpha
    exact Finset.prod_le_one (fun i _ => by linarith [s.beta_lt_one i])
      (fun i _ => by linarith [s.beta_pos i])
  have hsp : ∀ n : ℕ, alphaBar s (n + 1) = alphaBar s n * alpha s (n + 1) := by
    intro n; unfold alphaBar; rw [Finset.prod_Icc_succ_top (by omega)]
  have halp : ∀ n : ℕ, 0 < alpha s n := fun n => by unfold alpha; linarith [s.beta_lt_one n]
  have halp1 : ∀ n : ℕ, alpha s n < 1 := fun n => by unfold alpha; linarith [s.beta_pos n]
  have hblt : ∀ m : ℕ, 1 ≤ m → alphaBar s m < 1 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hsp k]
    nlinarith [hble k, hbpos k, halp (k + 1), halp1 (k + 1)]
  ---- coordinates and factorization
  have coord : ∀ y : Space d, ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
    intro y; rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [sq_abs]
  have chg : ∀ g : Space d → ℝ, ∫ y : Space d, g y = ∫ z : Fin d → ℝ, g (toLp 2 z) := fun g =>
    ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding g).symm
  have factorAll : ∀ (M : Space d) (v : ℝ), 0 < v → ∀ z : Space d,
      gaussPDF M v z = ∏ i, gaussianPDFReal (M i) v.toNNReal (z i) := by
    intro M v hv z
    have hvc : ((v.toNNReal : NNReal) : ℝ) = v := Real.coe_toNNReal v hv.le
    have hpos : (0:ℝ) < 2 * π * v := by positivity
    simp only [gaussianPDFReal, hvc, gaussPDF]
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
    congr 1
    · simp only [Finset.card_univ, Fintype.card_fin]
      rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 * π * v) ^ ((1:ℝ)/2)) d,
        ← Real.rpow_mul hpos.le, ← Real.rpow_neg hpos.le]
      congr 1; ring
    · rw [coord, ← Finset.sum_div, ← Finset.sum_neg_distrib]
      congr 1
  ---- one-dimensional Gaussian convolution
  have conv1D : ∀ m z c u w : ℝ, 0 < u → 0 < w →
      ∫ y : ℝ, gaussianPDFReal m u.toNNReal y * gaussianPDFReal (c * y) w.toNNReal z
        = gaussianPDFReal (c * m) (c ^ 2 * u + w).toNNReal z := by
    intro m z c u w hu hw
    have hS : 0 < c ^ 2 * u + w := by positivity
    have hu' : ((u.toNNReal : NNReal) : ℝ) = u := Real.coe_toNNReal u hu.le
    have hw' : ((w.toNNReal : NNReal) : ℝ) = w := Real.coe_toNNReal w hw.le
    have hS' : (((c ^ 2 * u + w).toNNReal : NNReal) : ℝ) = c ^ 2 * u + w :=
      Real.coe_toNNReal _ hS.le
    simp only [gaussianPDFReal, hu', hw', hS']
    have hexp : ∀ y : ℝ, -(y - m) ^ 2 / (2 * u) + -(z - c * y) ^ 2 / (2 * w)
        = -((c ^ 2 * u + w) / (2 * u * w)) *
            (y - (u * w / (c ^ 2 * u + w)) * (m / u + c * z / w)) ^ 2
          + -(z - c * m) ^ 2 / (2 * (c ^ 2 * u + w)) := by
      intro y; field_simp; ring
    have hrw : ∀ y : ℝ, (√(2 * π * u))⁻¹ * rexp (-(y - m) ^ 2 / (2 * u)) *
        ((√(2 * π * w))⁻¹ * rexp (-(z - c * y) ^ 2 / (2 * w)))
        = ((√(2 * π * u))⁻¹ * (√(2 * π * w))⁻¹ *
            rexp (-(z - c * m) ^ 2 / (2 * (c ^ 2 * u + w))))
          * rexp (-((c ^ 2 * u + w) / (2 * u * w)) *
              (y - (u * w / (c ^ 2 * u + w)) * (m / u + c * z / w)) ^ 2) := by
      intro y
      have hE : rexp (-(y - m) ^ 2 / (2 * u)) * rexp (-(z - c * y) ^ 2 / (2 * w))
          = rexp (-(z - c * m) ^ 2 / (2 * (c ^ 2 * u + w)))
            * rexp (-((c ^ 2 * u + w) / (2 * u * w)) *
                (y - (u * w / (c ^ 2 * u + w)) * (m / u + c * z / w)) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [hexp y]; ring
      rw [show (√(2 * π * u))⁻¹ * rexp (-(y - m) ^ 2 / (2 * u)) *
          ((√(2 * π * w))⁻¹ * rexp (-(z - c * y) ^ 2 / (2 * w)))
          = (√(2 * π * u))⁻¹ * (√(2 * π * w))⁻¹ *
            (rexp (-(y - m) ^ 2 / (2 * u)) * rexp (-(z - c * y) ^ 2 / (2 * w))) from by ring, hE]
      ring
    simp_rw [hrw]
    rw [integral_const_mul,
      integral_sub_right_eq_self (fun y : ℝ =>
        rexp (-((c ^ 2 * u + w) / (2 * u * w)) * y ^ 2))
        ((u * w / (c ^ 2 * u + w)) * (m / u + c * z / w)),
      integral_gaussian]
    have hconst : (√(2 * π * u))⁻¹ * (√(2 * π * w))⁻¹ *
        √(π / ((c ^ 2 * u + w) / (2 * u * w))) = (√(2 * π * (c ^ 2 * u + w)))⁻¹ := by
      rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_inv,
        ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    linear_combination (rexp (-(z - c * m) ^ 2 / (2 * (c ^ 2 * u + w)))) * hconst
  ---- the d-dimensional convolution
  have convD : ∀ (M : Space d) (u w c : ℝ), 0 < u → 0 < w → ∀ z : Space d,
      (∫ y : Space d, gaussPDF M u y * gaussPDF (c • y) w z)
        = gaussPDF (c • M) (c ^ 2 * u + w) z := by
    intro M u w c hu hw z
    have hS : 0 < c ^ 2 * u + w := by positivity
    rw [chg]
    have hfac : ∀ y : Fin d → ℝ,
        gaussPDF M u (toLp 2 y) * gaussPDF (c • (toLp 2 y : Space d)) w z
          = ∏ i, (gaussianPDFReal (M i) u.toNNReal (y i)
              * gaussianPDFReal (c * y i) w.toNNReal (z i)) := by
      intro y
      rw [factorAll M u hu, factorAll (c • (toLp 2 y : Space d)) w hw, ← Finset.prod_mul_distrib]
      rfl
    simp_rw [hfac]
    rw [integral_fintype_prod_volume_eq_prod fun i => fun r : ℝ =>
      gaussianPDFReal (M i) u.toNNReal r * gaussianPDFReal (c * r) w.toNNReal (z i)]
    rw [factorAll (c • M) (c ^ 2 * u + w) hS]
    exact Finset.prod_congr rfl fun i _ => conv1D (M i) (z i) c u w hu hw
  ---- induction on the number of steps
  suffices h : ∀ n : ℕ, ∀ z : Space d, qFwd s x0 (n + 1) z = qMarginal s (n + 1) x0 z by
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    exact h n x
  intro n
  induction n with
  | zero =>
    intro z
    have h1 : alphaBar s 1 = alpha s 1 := by
      unfold alphaBar; rw [Finset.Icc_self, Finset.prod_singleton]
    simp only [qFwd, qMarginal, h1]
    unfold alpha
    norm_num
  | succ k ih =>
    intro z
    have hstep : qFwd s x0 (k + 2) z
        = ∫ y : Space d, qFwd s x0 (k + 1) y *
            gaussPDF (Real.sqrt (1 - s.beta (k + 2)) • y) (s.beta (k + 2)) z := rfl
    rw [hstep]
    simp_rw [ih]
    have hu : (0:ℝ) < 1 - alphaBar s (k + 1) := by linarith [hblt (k + 1) (by omega)]
    have hsq : Real.sqrt (1 - s.beta (k + 2)) = Real.sqrt (alpha s (k + 2)) := by
      unfold alpha; ring_nf
    simp only [qMarginal, hsq]
    rw [convD (Real.sqrt (alphaBar s (k + 1)) • x0) (1 - alphaBar s (k + 1))
      (s.beta (k + 2)) (Real.sqrt (alpha s (k + 2))) hu (s.beta_pos (k + 2)) z]
    congr 1
    · rw [smul_smul, ← Real.sqrt_mul (halp (k + 2)).le, hsp (k + 1), mul_comm]
    · rw [Real.sq_sqrt (halp (k + 2)).le, hsp (k + 1)]
      unfold alpha
      ring
