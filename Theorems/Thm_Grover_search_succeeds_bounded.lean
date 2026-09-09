import Mathlib
import Definitions.Def_groverIterate
import Theorems.Thm_Grover_amplitude_rotation

namespace Grover

/-- **Grover's algorithm finds the marked item, in `O(√N)` iterations** (Goal). Starting from the
uniform superposition over `N` basis states, some number of applications of the Grover iterate,
bounded by `⌈π / (4·arcsin(1/√N))⌉` (which is `Θ(√N)`), produces a state in which the probability
of measuring the marked index `w0` is at least `1 - 1/N`. -/
theorem search_succeeds_bounded {N : ℕ} (w0 : Fin N) :
    ∃ k : ℕ, k ≤ ⌈Real.pi / (4 * Real.arcsin (1 / Real.sqrt N))⌉₊ ∧
      (1 : ℝ) - 1 / (N : ℝ) ≤
      ‖inner (𝕜 := ℂ) (EuclideanSpace.single w0 (1 : ℂ))
        ((⇑(groverIterate w0))^[k] (uniformSuperposition N))‖ ^ 2 := by
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
  have hθ0 : 0 < θ := by
    rw [hθ_def]
    exact Real.arcsin_pos.mpr (by positivity)
  have hθpi2 : θ ≤ Real.pi / 2 := by rw [hθ_def]; exact Real.arcsin_le_pi_div_two _
  set k := ⌊Real.pi / (4 * θ)⌋₊ with hk_def
  refine ⟨k, Nat.floor_le_ceil _, ?_⟩
  have hpos : (0 : ℝ) ≤ Real.pi / (4 * θ) := by positivity
  have hk_le : (k : ℝ) ≤ Real.pi / (4 * θ) := hk_def ▸ Nat.floor_le hpos
  have hk_lt : Real.pi / (4 * θ) < (k : ℝ) + 1 := hk_def ▸ Nat.lt_floor_add_one _
  have hbound1 : Real.pi / 2 - θ < (2 * (k : ℝ) + 1) * θ := by
    have h1 : Real.pi / 4 - θ < (k : ℝ) * θ := by
      rw [div_lt_iff₀ (by linarith)] at hk_lt
      nlinarith
    nlinarith
  have hbound2 : (2 * (k : ℝ) + 1) * θ ≤ Real.pi / 2 + θ := by
    have h2 : (k : ℝ) * θ ≤ Real.pi / 4 := by
      rw [le_div_iff₀ (by linarith)] at hk_le
      nlinarith
    nlinarith
  have hcosθ_nonneg : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθpi2⟩
  have hsin_ge : Real.cos θ ≤ Real.sin ((2 * (k : ℝ) + 1) * θ) := by
    have hsin_eq : Real.sin ((2 * (k : ℝ) + 1) * θ) = Real.cos (Real.pi / 2 - (2 * (k : ℝ) + 1) * θ) := by
      rw [Real.cos_pi_div_two_sub]
    rw [hsin_eq]
    have habs : |Real.pi / 2 - (2 * (k : ℝ) + 1) * θ| ≤ θ := by
      rw [abs_le]; constructor <;> linarith
    have h1 : (0 : ℝ) ≤ |Real.pi / 2 - (2 * (k : ℝ) + 1) * θ| := abs_nonneg _
    have h2 : θ ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi h1 h2 habs
    rwa [Real.cos_abs] at hmono
  have hsq : Real.cos θ ^ 2 ≤ Real.sin ((2 * (k : ℝ) + 1) * θ) ^ 2 := by
    apply sq_le_sq'
    · linarith [hcosθ_nonneg, hsin_ge]
    · exact hsin_ge
  have hcos2_eq : Real.cos θ ^ 2 = 1 - 1 / (N : ℝ) := by
    have hsinsq : Real.sin θ ^ 2 = 1 / (N : ℝ) := by
      rw [hsinθ, div_pow, Real.sq_sqrt (by positivity), one_pow]
    nlinarith [Real.sin_sq_add_cos_sq θ, hsinsq]
  have hampl := amplitude_rotation w0 k
  rw [← hθ_def] at hampl
  rw [hampl, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [hsq, hcos2_eq]

end Grover
