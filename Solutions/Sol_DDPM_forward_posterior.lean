import Definitions.Def_DDPM_process
open MeasureTheory Real
open DDPM

theorem solution {d : ℕ} (s : Schedule) (t : ℕ) (ht : 2 ≤ t) (x0 xt xprev : Space d) :
    gaussPDF (Real.sqrt (1 - s.beta t) • xprev) (s.beta t) xt * qMarginal s (t - 1) x0 xprev /
        qMarginal s t x0 xt
      = gaussPDF (posteriorMean s t xt x0) (posteriorVar s t) xprev := by
  -- ## generic helpers
  have nsq : ∀ (a b : Space d) (c : ℝ),
      ‖a - c • b‖ ^ 2 = ‖a‖ ^ 2 - 2 * c * (inner ℝ a b) + c ^ 2 * ‖b‖ ^ 2 := by
    intro a b c
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm b a]; ring
  have nsq2 : ∀ (a b c : Space d) (A B : ℝ),
      ‖a - (A • b + B • c)‖ ^ 2 = ‖a‖ ^ 2 - 2 * A * (inner ℝ a b) - 2 * B * (inner ℝ a c)
        + A ^ 2 * ‖b‖ ^ 2 + 2 * A * B * (inner ℝ b c) + B ^ 2 * ‖c‖ ^ 2 := by
    intro a b c A B
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm b a, real_inner_comm c a, real_inner_comm c b]; ring
  have key : ∀ v1 v2 v3 v4 E1 E2 E3 E4 : ℝ, 0 < v1 → 0 < v2 → 0 < v3 → 0 < v4 →
      v1 * v2 / v3 = v4 → E1 + E2 - E3 = E4 →
      (2 * π * v1) ^ (-(d : ℝ) / 2) * Real.exp E1 *
          ((2 * π * v2) ^ (-(d : ℝ) / 2) * Real.exp E2) /
          ((2 * π * v3) ^ (-(d : ℝ) / 2) * Real.exp E3)
        = (2 * π * v4) ^ (-(d : ℝ) / 2) * Real.exp E4 := by
    intro v1 v2 v3 v4 E1 E2 E3 E4 h1 h2 h3 h4 hv hE
    have hpi : (0:ℝ) < π := Real.pi_pos
    have hv' : v1 * v2 = v4 * v3 := by field_simp at hv; linarith
    have e1 : (2 * π * v1) ^ (-(d : ℝ) / 2) * (2 * π * v2) ^ (-(d : ℝ) / 2) /
        (2 * π * v3) ^ (-(d : ℝ) / 2) = (2 * π * v4) ^ (-(d : ℝ) / 2) := by
      rw [← Real.mul_rpow (by positivity) (by positivity),
        ← Real.div_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
      linear_combination hv'
    have hA3 : (2 * π * v3) ^ (-(d : ℝ) / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
    have hx3 : Real.exp E3 ≠ 0 := Real.exp_ne_zero E3
    rw [← e1, ← hE, Real.exp_sub, Real.exp_add]
    field_simp
  -- ## schedule facts
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
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  simp only [Nat.add_sub_cancel]
  have hsp : alphaBar s (n + 1) = alphaBar s n * alpha s (n + 1) := by
    unfold alphaBar; rw [Finset.prod_Icc_succ_top (by omega)]
  have hba : 0 < s.beta (n + 1) := s.beta_pos (n + 1)
  have hbn0 : 0 < alphaBar s n := hbpos n
  have hbn1 : alphaBar s n < 1 := hblt n hn
  have hbt1 : alphaBar s (n + 1) < 1 := hblt (n + 1) (by omega)
  have hon : (0:ℝ) < 1 - alphaBar s n := by linarith
  have hot : (0:ℝ) < 1 - alphaBar s (n + 1) := by linarith
  have hpv : 0 < posteriorVar s (n + 1) := by
    unfold posteriorVar
    simp only [Nat.add_sub_cancel]
    positivity
  -- ## square-root parameters
  have halp : 0 < alpha s (n + 1) := by unfold alpha; linarith [s.beta_lt_one (n + 1)]
  obtain ⟨u, hupos, hu2⟩ : ∃ u : ℝ, 0 < u ∧ u ^ 2 = alphaBar s n :=
    ⟨Real.sqrt (alphaBar s n), Real.sqrt_pos.mpr hbn0, Real.sq_sqrt hbn0.le⟩
  obtain ⟨w, hwpos, hw2⟩ : ∃ w : ℝ, 0 < w ∧ w ^ 2 = alpha s (n + 1) :=
    ⟨Real.sqrt (alpha s (n + 1)), Real.sqrt_pos.mpr halp, Real.sq_sqrt halp.le⟩
  have hsu : Real.sqrt (alphaBar s n) = u := by rw [← hu2, Real.sqrt_sq hupos.le]
  have hsw : Real.sqrt (alpha s (n + 1)) = w := by rw [← hw2, Real.sqrt_sq hwpos.le]
  have hsb : Real.sqrt (1 - s.beta (n + 1)) = w := by
    have h : 1 - s.beta (n + 1) = alpha s (n + 1) := by unfold alpha; ring
    rw [h, hsw]
  have hst : Real.sqrt (alphaBar s (n + 1)) = u * w := by
    rw [hsp, Real.sqrt_mul hbn0.le, hsu, hsw]
  have hbb : s.beta (n + 1) = 1 - w ^ 2 := by rw [hw2]; unfold alpha; ring
  -- ## assemble
  simp only [qMarginal, gaussPDF]
  refine key _ _ _ _ _ _ _ _ hba hon hot hpv ?_ ?_
  · unfold posteriorVar
    simp only [Nat.add_sub_cancel]
    field_simp
  · unfold posteriorMean posteriorVar
    simp only [Nat.add_sub_cancel, hst, hsb, hsu, hsw, nsq, nsq2]
    rw [real_inner_comm xprev xt, real_inner_comm x0 xt]
    rw [hsp, ← hu2, ← hw2, hbb]
    have e1 : (1 : ℝ) - u ^ 2 = 1 - alphaBar s n := by rw [hu2]
    have e2 : (1 : ℝ) - w ^ 2 = s.beta (n + 1) := by rw [hw2]; unfold alpha; ring
    have e3 : (1 : ℝ) - u ^ 2 * w ^ 2 = 1 - alphaBar s (n + 1) := by rw [hu2, hw2, ← hsp]
    have e3' : (1 : ℝ) - w ^ 2 * u ^ 2 = 1 - alphaBar s (n + 1) := by
      rw [← e3]; ring
    have d1 : (1 : ℝ) - u ^ 2 ≠ 0 := by rw [e1]; exact ne_of_gt hon
    have d2 : (1 : ℝ) - w ^ 2 ≠ 0 := by rw [e2]; exact ne_of_gt hba
    have d3 : (1 : ℝ) - u ^ 2 * w ^ 2 ≠ 0 := by rw [e3]; exact ne_of_gt hot
    have d3' : (1 : ℝ) - w ^ 2 * u ^ 2 ≠ 0 := by rw [e3']; exact ne_of_gt hot
    have du : u ≠ 0 := ne_of_gt hupos
    have dw : w ≠ 0 := ne_of_gt hwpos
    field_simp
    ring
