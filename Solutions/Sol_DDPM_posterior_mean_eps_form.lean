import Definitions.Def_DDPM_process
open MeasureTheory Real
open DDPM

theorem solution {d : ℕ} (s : Schedule) (t : ℕ) (ht : 1 ≤ t) (xt e : Space d) :
    posteriorMean s t xt ((1 / Real.sqrt (alphaBar s t)) • (xt - Real.sqrt (1 - alphaBar s t) • e))
      = (1 / Real.sqrt (alpha s t)) • (xt - (s.beta t / Real.sqrt (1 - alphaBar s t)) • e) := by
  have hbpos : ∀ m : ℕ, 0 < alphaBar s m := by
    intro m
    unfold alphaBar alpha
    exact Finset.prod_pos fun i _ => by linarith [s.beta_lt_one i]
  have hble : ∀ m : ℕ, alphaBar s m ≤ 1 := by
    intro m
    unfold alphaBar alpha
    exact Finset.prod_le_one (fun i _ => by linarith [s.beta_lt_one i])
      (fun i _ => by linarith [s.beta_pos i])
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hsplit : alphaBar s (n + 1) = alphaBar s n * alpha s (n + 1) := by
    unfold alphaBar
    rw [Finset.prod_Icc_succ_top (by omega)]
  have ha : 0 < alpha s (n + 1) := by unfold alpha; linarith [s.beta_lt_one (n + 1)]
  have hb : s.beta (n + 1) = 1 - alpha s (n + 1) := by unfold alpha; ring
  have hbn : 0 < alphaBar s n := hbpos n
  have hlt : alphaBar s (n + 1) < 1 := by
    rw [hsplit]
    nlinarith [hble n, s.beta_pos (n + 1), s.beta_lt_one (n + 1)]
  have hone : (0:ℝ) < 1 - alphaBar s (n + 1) := by linarith
  have hs1 : Real.sqrt (alphaBar s (n + 1))
      = Real.sqrt (alphaBar s n) * Real.sqrt (alpha s (n + 1)) := by
    rw [hsplit, Real.sqrt_mul hbn.le]
  have hsn : 0 < Real.sqrt (alphaBar s n) := Real.sqrt_pos.mpr hbn
  have hsa : 0 < Real.sqrt (alpha s (n + 1)) := Real.sqrt_pos.mpr ha
  have hso : 0 < Real.sqrt (1 - alphaBar s (n + 1)) := Real.sqrt_pos.mpr hone
  have hsa2 : Real.sqrt (alpha s (n + 1)) ^ 2 = alpha s (n + 1) := Real.sq_sqrt ha.le
  have hso2 : Real.sqrt (1 - alphaBar s (n + 1)) ^ 2 = 1 - alphaBar s (n + 1) :=
    Real.sq_sqrt hone.le
  simp only [posteriorMean, Nat.add_sub_cancel, hs1, hb, smul_sub, smul_smul]
  match_scalars
  · field_simp
    nlinarith [hsa2, hso2, hsplit, hsn, hsa, hso, hbn]
  · field_simp
    nlinarith [hsa2, hso2, hsplit, hsn, hsa, hso, hbn]
