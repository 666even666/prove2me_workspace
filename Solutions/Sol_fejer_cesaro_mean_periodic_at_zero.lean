import Mathlib
import Theorems.Thm_Fejer_fejer_theorem
import Definitions.Def_Fejer_fourierCoeff
import Definitions.Def_Fejer_partialSum
import Definitions.Def_Fejer_cesaroMean

open MeasureTheory Filter

theorem solution
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (hf_cont : Continuous f)
    (hf_periodic : ∀ x : ℝ, f (x + T) = f x)
    (α : ℤ → ℝ)
    (hα : ∀ k : ℤ, α k =
      (1 / T) * ∫ x in (0 : ℝ)..T, f x * Real.cos (2 * Real.pi * (k : ℝ) * x / T)) :
    Filter.Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) *
        ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.Icc (-(n : ℤ)) n, α k)
      Filter.atTop (nhds (f 0)) := by
  have hTne : T ≠ 0 := hT.ne'
  have hTneC : (T : ℂ) ≠ 0 := by exact_mod_cast hTne
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := hπpos.ne'
  -- The `2π`-periodic complex rescaling of `f`.
  set g : ℝ → ℂ := fun θ => (f (T * θ / (2 * Real.pi)) : ℂ) with hgdef
  have hg_cont : Continuous g := Complex.continuous_ofReal.comp (by fun_prop)
  have hg_per : Function.Periodic g (2 * Real.pi) := by
    intro θ
    have hshift : T * (θ + 2 * Real.pi) / (2 * Real.pi) = T * θ / (2 * Real.pi) + T := by
      field_simp
    simp only [hgdef, hshift, hf_periodic]
  -- **Step 1: coefficient identity.** `fourierCoeff g k` is the classical `T`-periodic complex
  -- Fourier coefficient of `f`, via the linear substitution `θ = 2πx/T` and a periodicity shift.
  have hcoeff : ∀ k : ℤ, Fejer.fourierCoeff g k =
      (1 / (T : ℂ)) * ∫ x in (0 : ℝ)..T,
        (f x : ℂ) * Complex.exp (((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I) := by
    intro k
    set F : ℝ → ℂ := fun x =>
      (f x : ℂ) * Complex.exp (((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I)
      with hFdef
    have hFper : Function.Periodic F T := by
      intro x
      simp only [hFdef, hf_periodic x]
      rw [show ((-(2 * Real.pi * (k : ℝ) * (x + T) / T) : ℝ) : ℂ) * Complex.I
          = ((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I
            + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
          from by push_cast; field_simp [hTneC]; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
      ring
    have hcne : (2 * Real.pi / T : ℝ) ≠ 0 := by positivity
    have hHeq : ∀ x : ℝ,
        g (2 * Real.pi / T * x) *
          Complex.exp (-(k : ℂ) * ((2 * Real.pi / T * x : ℝ) : ℂ) * Complex.I) = F x := by
      intro x
      have hgval : g (2 * Real.pi / T * x) = (f x : ℂ) := by
        simp only [hgdef]; congr 1; field_simp
      have hexp_eq : -(k : ℂ) * ((2 * Real.pi / T * x : ℝ) : ℂ)
          = ((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hgval, hexp_eq, hFdef]
    have hbounds1 : (2 * Real.pi / T) * (-(T / 2)) = -Real.pi := by field_simp
    have hbounds2 : (2 * Real.pi / T) * (T / 2) = Real.pi := by field_simp
    have hsub := intervalIntegral.integral_comp_mul_left
      (fun θ : ℝ => g θ * Complex.exp (-(k : ℂ) * θ * Complex.I)) hcne
      (a := -(T / 2)) (b := T / 2)
    rw [hbounds1, hbounds2] at hsub
    simp only [hHeq] at hsub
    -- hsub : ∫ x in -(T/2)..(T/2), F x = (2π/T)⁻¹ • ∫ θ in -π..π, g θ * exp(-(k:ℂ)*θ*I)
    have hTP : (∫ x in (-(T / 2))..(T / 2), F x) = ∫ x in (0 : ℝ)..T, F x := by
      have hshift := hFper.intervalIntegral_add_eq (-(T / 2)) 0
      rw [show (-(T / 2) : ℝ) + T = T / 2 from by ring, zero_add] at hshift
      exact hshift
    rw [hTP] at hsub
    have hscal : (2 * Real.pi / T : ℝ) • (∫ x in (0 : ℝ)..T, F x)
        = ∫ θ in (-Real.pi)..Real.pi, g θ * Complex.exp (-(k : ℂ) * θ * Complex.I) := by
      rw [hsub, smul_smul, mul_inv_cancel₀ hcne, one_smul]
    have hfc : Fejer.fourierCoeff g k
        = (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi,
            g θ * Complex.exp (-(k : ℂ) * θ * Complex.I) := rfl
    rw [hfc, ← hscal, Complex.real_smul]
    push_cast
    field_simp
  -- **Step 2: the partial sum at `0` is the symmetric sum of `α`.**
  have hpartial : ∀ n : ℕ,
      Fejer.partialSum g n 0 = ((∑ k ∈ Finset.Icc (-(n : ℤ)) n, α k : ℝ) : ℂ) := by
    intro n
    have hstep1 : Fejer.partialSum g n 0
        = ∑ k ∈ Finset.Icc (-(n : ℤ)) n, Fejer.fourierCoeff g k := by
      simp [Fejer.partialSum]
    rw [hstep1]
    simp_rw [hcoeff, ← Finset.mul_sum]
    have hswap : ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        ∫ x in (0 : ℝ)..T,
          (f x : ℂ) * Complex.exp (((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I)
        = ∫ x in (0 : ℝ)..T, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
            (f x : ℂ) * Complex.exp (((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I) := by
      rw [intervalIntegral.integral_finsetSum]
      intro k _
      apply Continuous.intervalIntegrable
      fun_prop
    rw [hswap]
    have hpt : ∀ x : ℝ, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (f x : ℂ) * Complex.exp (((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I)
        = ((f x * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, Real.cos (2 * Real.pi * (k : ℝ) * x / T) : ℝ)
            : ℂ) := by
      intro x
      have heuler : ∀ k : ℤ, Complex.exp (((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I)
          = ((Real.cos (2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ)
              - Complex.I * ((Real.sin (2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) := by
        intro k
        rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
        push_cast; ring
      have hsin0 : ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          ((Real.sin (2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) = 0 := by
        have hreal0 : ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
            Real.sin (2 * Real.pi * (k : ℝ) * x / T) = 0 := by
          have hreindex : ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
              Real.sin (2 * Real.pi * (k : ℝ) * x / T)
              = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
                  Real.sin (2 * Real.pi * ((-k : ℤ) : ℝ) * x / T) := by
            apply Finset.sum_nbij' (i := fun k : ℤ => -k) (j := fun k : ℤ => -k)
            · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
            · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
            · intro a _; simp
            · intro a _; simp
            · intro a _; simp
          have hneg : ∀ k : ℤ, Real.sin (2 * Real.pi * ((-k : ℤ) : ℝ) * x / T)
              = -Real.sin (2 * Real.pi * (k : ℝ) * x / T) := by
            intro k
            rw [show 2 * Real.pi * ((-k : ℤ) : ℝ) * x / T = -(2 * Real.pi * (k : ℝ) * x / T)
                from by push_cast; ring, Real.sin_neg]
          simp_rw [hneg] at hreindex
          rw [Finset.sum_neg_distrib] at hreindex
          linarith
        rw [← Complex.ofReal_sum, hreal0, Complex.ofReal_zero]
      simp_rw [heuler, mul_sub]
      rw [Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum]
      rw [hsin0]
      simp only [mul_zero, sub_zero]
      rw [← Complex.ofReal_sum, ← Complex.ofReal_mul]
    simp_rw [hpt]
    rw [intervalIntegral.integral_ofReal]
    have hswapr : ∫ x in (0 : ℝ)..T,
          f x * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, Real.cos (2 * Real.pi * (k : ℝ) * x / T)
        = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
            ∫ x in (0 : ℝ)..T, f x * Real.cos (2 * Real.pi * (k : ℝ) * x / T) := by
      simp_rw [Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum]
      intro k _
      apply Continuous.intervalIntegrable
      fun_prop
    rw [hswapr]
    have hαk : ∀ k : ℤ, (∫ x in (0 : ℝ)..T, f x * Real.cos (2 * Real.pi * (k : ℝ) * x / T))
        = T * α k := by
      intro k; rw [hα k]; field_simp
    simp_rw [hαk, ← Finset.mul_sum]
    rw [show (1:ℂ)/(T:ℂ) * ((T * ∑ k ∈ Finset.Icc (-(n:ℤ)) n, α k : ℝ):ℂ)
        = ((∑ k ∈ Finset.Icc (-(n:ℤ)) n, α k : ℝ):ℂ) from by
      rw [Complex.ofReal_mul]
      push_cast
      field_simp]
  -- **Step 3: apply Fejér's theorem to `g` and evaluate pointwise at `0`.**
  have hfejer := Fejer.fejer_theorem g hg_cont hg_per
  have hpt0 := hfejer.tendsto_at 0
  -- hpt0 : Tendsto (fun N => Fejer.cesaroMean g N 0) atTop (nhds (g 0))
  have hg0 : g 0 = (f 0 : ℂ) := by simp [hgdef]
  rw [hg0] at hpt0
  have hce : ∀ N : ℕ, Fejer.cesaroMean g N 0
      = ((1 / ((N : ℝ) + 1)) *
          ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.Icc (-(n : ℤ)) n, α k : ℝ) := by
    intro N
    show (1 / ((N : ℂ) + 1)) * ∑ n ∈ Finset.range (N + 1), Fejer.partialSum g n 0 = _
    simp_rw [hpartial]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_one, ← Complex.ofReal_natCast,
      ← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_mul]
  simp_rw [hce] at hpt0
  exact Filter.tendsto_ofReal_iff.mp hpt0
