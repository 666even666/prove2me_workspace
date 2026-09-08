import Mathlib
import Definitions.Def_groverIterate

open Grover

theorem solution {N : ℕ} (w0 : Fin N) (x : EuclideanSpace ℂ (Fin N)) :
    ‖(groverIterate w0) x‖ = ‖x‖ := by
  have reflect_isometry : ∀ (u : EuclideanSpace ℂ (Fin N)), ‖u‖ = 1 →
      ∀ v : EuclideanSpace ℂ (Fin N),
      ‖(2 : ℂ) • (inner (𝕜 := ℂ) u v : ℂ) • u - v‖ = ‖v‖ := by
    intro u hu v
    have key : ‖(2 : ℂ) • (inner (𝕜 := ℂ) u v : ℂ) • u - v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := ℂ) ((2 : ℂ) • (inner (𝕜 := ℂ) u v : ℂ) • u) v, smul_smul]
      have hn : ‖(2 * (inner (𝕜 := ℂ) u v : ℂ)) • u‖ ^ 2
          = 4 * ‖(inner (𝕜 := ℂ) u v : ℂ)‖ ^ 2 := by
        rw [norm_smul, mul_pow, hu, one_pow, mul_one, norm_mul]
        rw [show ‖(2:ℂ)‖ = 2 by norm_num]
        ring
      have hre : RCLike.re (inner (𝕜 := ℂ) ((2 * (inner (𝕜 := ℂ) u v : ℂ)) • u) v)
          = 2 * ‖(inner (𝕜 := ℂ) u v : ℂ)‖ ^ 2 := by
        rw [inner_smul_left]
        have hc : (starRingEnd ℂ) (2 * (inner (𝕜 := ℂ) u v : ℂ)) * (inner (𝕜 := ℂ) u v : ℂ)
            = 2 * ((starRingEnd ℂ) (inner (𝕜 := ℂ) u v : ℂ) * (inner (𝕜 := ℂ) u v : ℂ)) := by
          rw [map_mul]
          have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
          rw [h2]
          ring
        rw [hc, RCLike.conj_mul]
        simp [← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hn, hre]
      ring
    nlinarith [key, norm_nonneg ((2 : ℂ) • (inner (𝕜 := ℂ) u v : ℂ) • u - v), norm_nonneg v]
  have he : ‖(EuclideanSpace.single w0 (1 : ℂ) : EuclideanSpace ℂ (Fin N))‖ = 1 := by simp
  have hNpos : 0 < N := w0.pos
  have hs : ‖(uniformSuperposition N : EuclideanSpace ℂ (Fin N))‖ = 1 := by
    have hsq : ‖(uniformSuperposition N : EuclideanSpace ℂ (Fin N))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
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
    nlinarith [hsq, norm_nonneg (uniformSuperposition N : EuclideanSpace ℂ (Fin N))]
  have h_oracle : ∀ v, ‖oracle w0 v‖ = ‖v‖ := by
    intro v
    have hrw : oracle w0 v
        = -((2 : ℂ) • (inner (𝕜 := ℂ) (EuclideanSpace.single w0 (1 : ℂ)) v : ℂ) •
            EuclideanSpace.single w0 (1 : ℂ) - v) := by
      unfold oracle
      simp only [sub_apply, ContinuousLinearMap.id_apply,
        smul_apply, InnerProductSpace.rankOne_apply]
      abel
    rw [hrw, norm_neg]
    exact reflect_isometry (EuclideanSpace.single w0 (1 : ℂ)) he v
  have h_diffusion : ∀ v, ‖diffusion N v‖ = ‖v‖ := by
    intro v
    have hrw : diffusion N v
        = (2 : ℂ) • (inner (𝕜 := ℂ) (uniformSuperposition N) v : ℂ) •
            uniformSuperposition N - v := by
      unfold diffusion
      simp only [sub_apply, ContinuousLinearMap.id_apply,
        smul_apply, InnerProductSpace.rankOne_apply]
    rw [hrw]
    exact reflect_isometry (uniformSuperposition N) hs v
  have : groverIterate w0 x = diffusion N (oracle w0 x) := by
    unfold groverIterate
    simp only [ContinuousLinearMap.comp_apply]
  rw [this, h_diffusion, h_oracle]
