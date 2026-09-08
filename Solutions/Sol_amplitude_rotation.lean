import Mathlib
import Definitions.Def_groverIterate

open Grover

theorem solution {N : ℕ} (w0 : Fin N) (k : ℕ) :
    inner (𝕜 := ℂ) (EuclideanSpace.single w0 (1 : ℂ))
      ((⇑(groverIterate w0))^[k] (uniformSuperposition N)) =
    (Real.sin ((2 * k + 1) * Real.arcsin (1 / Real.sqrt N)) : ℂ) := by
  have hNpos : 0 < N := w0.pos
  have hNnn : (0 : ℝ) ≤ 1 / Real.sqrt N := by positivity
  have hNle1 : 1 / Real.sqrt N ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ Real.sqrt N := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hNpos)
    linarith
  set θ := Real.arcsin (1 / Real.sqrt N) with hθ_def
  have hsinθ : Real.sin θ = 1 / Real.sqrt N := Real.sin_arcsin (by linarith) hNle1
  set e : EuclideanSpace ℂ (Fin N) := EuclideanSpace.single w0 (1 : ℂ) with he_def
  set s : EuclideanSpace ℂ (Fin N) := uniformSuperposition N with hs_def
  have he_norm : ‖e‖ = 1 := by rw [he_def]; simp
  have he_e : (inner (𝕜 := ℂ) e e : ℂ) = 1 := by rw [he_def]; simp
  have he_s : (inner (𝕜 := ℂ) e s : ℂ) = (Real.sin θ : ℂ) := by
    rw [he_def, hs_def, EuclideanSpace.inner_single_left, hsinθ]
    simp [uniformSuperposition]
  have hs_e : (inner (𝕜 := ℂ) s e : ℂ) = (Real.sin θ : ℂ) := by
    rw [he_def, hs_def, EuclideanSpace.inner_single_right, hsinθ]
    simp [uniformSuperposition]
  have hs_norm_sq : ‖s‖ ^ 2 = 1 := by
    rw [hs_def, EuclideanSpace.norm_sq_eq]
    have hterm : ∀ i : Fin N,
        ‖(uniformSuperposition N : EuclideanSpace ℂ (Fin N)) i‖ ^ 2 = 1 / (N : ℝ) := by
      intro i
      show ‖(((1 / Real.sqrt N : ℝ) : ℂ))‖ ^ 2 = 1 / (N : ℝ)
      rw [Complex.norm_real, Real.norm_eq_abs]
      rw [show (1 : ℝ) / Real.sqrt N = Real.sqrt (1 / N) by
        rw [Real.sqrt_div' 1 (by norm_num), Real.sqrt_one]]
      rw [sq_abs, Real.sq_sqrt (by positivity)]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
    field_simp
  have hs_norm : ‖s‖ = 1 := by nlinarith [hs_norm_sq, norm_nonneg s]
  -- h := s - sinθ • e (unnormalized orthogonal residual)
  have hh_norm_sq : ‖s - (Real.sin θ : ℂ) • e‖ ^ 2 = Real.cos θ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ) s ((Real.sin θ : ℂ) • e), hs_norm, norm_smul, he_norm, mul_one]
    have habs : ‖(Real.sin θ : ℂ)‖ = |Real.sin θ| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [habs, sq_abs]
    have hre : RCLike.re (inner (𝕜 := ℂ) s ((Real.sin θ : ℂ) • e)) = Real.sin θ * Real.sin θ := by
      rw [inner_smul_right, hs_e, ← Complex.ofReal_mul]
      exact Complex.ofReal_re _
    rw [hre]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have he_h : (inner (𝕜 := ℂ) e (s - (Real.sin θ : ℂ) • e) : ℂ) = 0 := by
    rw [inner_sub_right, inner_smul_right, he_s, he_e]
    push_cast
    ring
  set g : EuclideanSpace ℂ (Fin N) := (Real.cos θ : ℂ)⁻¹ • (s - (Real.sin θ : ℂ) • e) with hg_def
  have he_g : (inner (𝕜 := ℂ) e g : ℂ) = 0 := by
    rw [hg_def, inner_smul_right, he_h, mul_zero]
  have hs_decomp : s = (Real.sin θ : ℂ) • e + (Real.cos θ : ℂ) • g := by
    rcases eq_or_ne (Real.cos θ) 0 with hc0 | hc0
    · have hh0 : s - (Real.sin θ : ℂ) • e = 0 := by
        have hz : ‖s - (Real.sin θ : ℂ) • e‖ ^ 2 = 0 := by rw [hh_norm_sq, hc0]; ring
        have hnorm0 : ‖s - (Real.sin θ : ℂ) • e‖ = 0 := by
          nlinarith [norm_nonneg (s - (Real.sin θ : ℂ) • e)]
        exact norm_eq_zero.mp hnorm0
      have hse : s = (Real.sin θ : ℂ) • e := sub_eq_zero.mp hh0
      rw [hg_def, hh0, smul_zero, smul_zero, add_zero]
      exact hse
    · rw [hg_def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hc0 : (Real.cos θ : ℂ) ≠ 0), one_smul]
      abel
  have hreal_pyth : (1 : ℝ) - Real.sin θ * Real.sin θ = Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsh : (inner (𝕜 := ℂ) s (s - (Real.sin θ : ℂ) • e) : ℂ) = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hs_norm, hs_e]
    push_cast
    norm_cast
    norm_num
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have key_identity : ∀ a : ℂ, a⁻¹ * a ^ 2 = a := by
    intro a
    rcases eq_or_ne a 0 with ha | ha
    · simp [ha]
    · field_simp
  have hsg : (inner (𝕜 := ℂ) s g : ℂ) = (Real.cos θ : ℂ) := by
    rw [hg_def, inner_smul_right, hsh, show ((Real.cos θ ^ 2 : ℝ) : ℂ) = (Real.cos θ : ℂ) ^ 2 by
      push_cast; ring]
    exact key_identity (Real.cos θ : ℂ)
  have oracle_eq : ∀ v : EuclideanSpace ℂ (Fin N),
      oracle w0 v = v - ((2 : ℂ) * (inner (𝕜 := ℂ) e v : ℂ)) • e := by
    intro v
    rw [he_def]
    unfold oracle
    simp only [sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      InnerProductSpace.rankOne_apply, smul_smul]
  have diffusion_eq : ∀ v : EuclideanSpace ℂ (Fin N),
      diffusion N v = ((2 : ℂ) * (inner (𝕜 := ℂ) s v : ℂ)) • s - v := by
    intro v
    rw [hs_def]
    unfold diffusion
    simp only [sub_apply, ContinuousLinearMap.id_apply, smul_apply,
      InnerProductSpace.rankOne_apply, smul_smul]
  have G_eq : ∀ v : EuclideanSpace ℂ (Fin N), groverIterate w0 v = diffusion N (oracle w0 v) := by
    intro v
    unfold groverIterate
    simp only [ContinuousLinearMap.comp_apply]
  have O_e : oracle w0 e = -e := by
    rw [oracle_eq, he_e, mul_one]
    module
  have O_g : oracle w0 g = g := by
    rw [oracle_eq, he_g, mul_zero, zero_smul, sub_zero]
  have hcos2 : Real.cos (2 * θ) = 1 - 2 * Real.sin θ * Real.sin θ := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hcos2' : Real.cos (2 * θ) = 2 * Real.cos θ * Real.cos θ - 1 := by
    rw [Real.cos_two_mul]; ring
  have hcos2C : (Real.cos (2 * θ) : ℂ) = 1 - 2 * (Real.sin θ : ℂ) * (Real.sin θ : ℂ) := by
    rw [hcos2]; norm_cast
  have hcos2C' : (Real.cos (2 * θ) : ℂ) = 2 * (Real.cos θ : ℂ) * (Real.cos θ : ℂ) - 1 := by
    rw [hcos2']; norm_cast
  have hsin2C : (Real.sin (2 * θ) : ℂ) = 2 * (Real.sin θ : ℂ) * (Real.cos θ : ℂ) := by
    rw [hsin2]; norm_cast
  have G_e : groverIterate w0 e = (Real.cos (2 * θ) : ℂ) • e - (Real.sin (2 * θ) : ℂ) • g := by
    rw [G_eq, O_e, diffusion_eq,
      show (inner (𝕜 := ℂ) s (-e) : ℂ) = -(Real.sin θ : ℂ) by rw [inner_neg_right, hs_e]]
    rw [hs_decomp, hcos2C, hsin2C]
    module
  have G_g : groverIterate w0 g = (Real.sin (2 * θ) : ℂ) • e + (Real.cos (2 * θ) : ℂ) • g := by
    rw [G_eq, O_g, diffusion_eq, hsg]
    rw [hs_decomp, hcos2C', hsin2C]
    module
  -- Induction: (G^[n]) s = sin((2n+1)θ)•e + cos((2n+1)θ)•g
  have hind : ∀ n : ℕ, (⇑(groverIterate w0))^[n] s =
      (Real.sin ((2 * n + 1) * θ) : ℂ) • e + (Real.cos ((2 * n + 1) * θ) : ℂ) • g := by
    intro n
    induction n with
    | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.cast_zero]
      rw [show (2 * (0 : ℝ) + 1) * θ = θ by ring]
      exact hs_decomp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_add, map_smul, map_smul, G_e, G_g]
      simp only [Nat.cast_add, Nat.cast_one]
      have hangle : (2 * ((n : ℝ) + 1) + 1) * θ = (2 * n + 1) * θ + 2 * θ := by ring
      rw [hangle, Real.sin_add, Real.cos_add]
      simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
      module
  rw [hind k, inner_add_right, inner_smul_right, inner_smul_right, he_e, he_g]
  ring
