import Mathlib
import Definitions.Def_PositiveDefiniteKernel
import Theorems.Thm_ClockRoPE_posDef_continuous_extension
import Theorems.Thm_ClockRoPE_fejer_cesaro_mean_periodic_at_zero

open MeasureTheory intervalIntegral Filter
open ClockRoPE
/-- **Corollary 3.3 (Periodic Case via Herglotz's Theorem)** — corrected against
`IsPositiveDefiniteKernel`, superseding `ClockRoPE.periodic_posdef_fourier_coeffs_pmf`, which
used the under-hypothesized `IsPosDefKernel`.
Let `f : ℝ → ℝ` be a continuous, positive-definite, `T`-periodic kernel with `f 0 = 1`
(`T > 0`), with (real) Fourier coefficients `α_k = (1/T) ∫_0^T f(x) cos(2πkx/T) dx` for
`k ∈ ℤ` (the source's Eq. (14) gives this as equal to the complex-exponential form
`(1/T) ∫_0^T f(x) e^{-i2πkx/T} dx`; the real cosine form is used here so that `α k` is
manifestly a real number). By Herglotz's theorem, `{α_k}` are all nonnegative and sum to
`f 0 = 1`, i.e. they form a valid probability mass function over the discrete harmonics
`{k / T}`. -/
theorem solution
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hf_cont : Continuous f) (hf_pd : IsPositiveDefiniteKernel f) (hf0 : f 0 = 1)
    (hf_periodic : ∀ x : ℝ, f (x + T) = f x)
    (α : ℤ → ℝ)
    (hα : ∀ k : ℤ, α k =
      (1 / T) * ∫ x in (0 : ℝ)..T, f x * Real.cos (2 * Real.pi * (k : ℝ) * x / T)) :
    (∀ k : ℤ, 0 ≤ α k) ∧ ∑' k : ℤ, α k = 1 := by
  have hf_even : ∀ x : ℝ, f (-x) = f x := hf_pd.even
  have hTne : T ≠ 0 := hT.ne'
  have hTneC : (T : ℂ) ≠ 0 := by exact_mod_cast hTne
  -- **Part 1: nonnegativity.** Evaluate the continuous extension of positive-definiteness at
  -- the character `φ(x) = exp(-2πikx/T)`.
  have hnonneg : ∀ k : ℤ, 0 ≤ α k := by
    intro k
    set φ : ℝ → ℂ := fun x => Complex.exp (((-(2 * Real.pi * (k : ℝ) * x / T) : ℝ) : ℂ) * Complex.I)
      with hφdef
    have hφcont : Continuous φ := by fun_prop
    have hext := posDef_continuous_extension f hf_cont hf_pd 0 T φ hφcont
    -- The integrand simplifies to a single character times `f (x - y)`.
    set F : ℝ → ℂ := fun u =>
      Complex.exp (((2 * Real.pi * (k : ℝ) * u / T : ℝ) : ℂ) * Complex.I) * (f u : ℂ)
      with hFdef
    have hpt : ∀ x y : ℝ,
        (starRingEnd ℂ) (φ x) * φ y * (f (x - y) : ℂ) = F (x - y) := by
      intro x y
      simp only [hφdef, hFdef]
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    -- `F` is `T`-periodic.
    have hFper : Function.Periodic F T := by
      intro u
      simp only [hFdef, hf_periodic u]
      rw [show (((2 * Real.pi * (k : ℝ) * (u + T) / T : ℝ) : ℂ) * Complex.I)
          = ((2 * Real.pi * (k : ℝ) * u / T : ℝ) : ℂ) * Complex.I
            + (k : ℂ) * (2 * Real.pi * Complex.I) from by
        push_cast
        field_simp [hTneC],
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
      ring
    -- The inner integral (over `y`) does not depend on `x`.
    have hinner : ∀ x : ℝ, ∫ y in (0 : ℝ)..T, (starRingEnd ℂ) (φ x) * φ y * (f (x - y) : ℂ)
        = ∫ u in (0 : ℝ)..T, F u := by
      intro x
      have step1 : (∫ y in (0 : ℝ)..T, (starRingEnd ℂ) (φ x) * φ y * (f (x - y) : ℂ))
          = ∫ y in (0 : ℝ)..T, F (x - y) :=
        intervalIntegral.integral_congr (fun y _ => hpt x y)
      rw [step1, intervalIntegral.integral_comp_sub_left F x]
      have step2 := hFper.intervalIntegral_add_eq (x - T) 0
      simpa using step2
    -- Hence the double integral is `T` times a constant, `T • ∫ u in 0..T, F u`.
    have hdouble : (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
        (starRingEnd ℂ) (φ x) * φ y * (f (x - y) : ℂ))
        = (T : ℂ) * ∫ u in (0 : ℝ)..T, F u := by
      simp_rw [hinner]
      rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
    -- Split `∫ u in 0..T, F u` into its cosine (real) and sine (imaginary) parts.
    have hFsplit : (∫ u in (0 : ℝ)..T, F u)
        = ((∫ u in (0 : ℝ)..T, f u * Real.cos (2 * Real.pi * (k : ℝ) * u / T) : ℝ) : ℂ)
          + Complex.I * ((∫ u in (0 : ℝ)..T, f u * Real.sin (2 * Real.pi * (k : ℝ) * u / T) : ℝ)
            : ℂ) := by
      have hpt2 : ∀ u : ℝ, F u
          = ((f u * Real.cos (2 * Real.pi * (k : ℝ) * u / T) : ℝ) : ℂ)
            + Complex.I * ((f u * Real.sin (2 * Real.pi * (k : ℝ) * u / T) : ℝ) : ℂ) := by
        intro u
        simp only [hFdef, Complex.exp_ofReal_mul_I]
        push_cast
        ring
      have hf1cont : Continuous (fun u : ℝ =>
          ((f u * Real.cos (2 * Real.pi * (k : ℝ) * u / T) : ℝ) : ℂ)) := by fun_prop
      have hf2cont : Continuous (fun u : ℝ =>
          Complex.I * ((f u * Real.sin (2 * Real.pi * (k : ℝ) * u / T) : ℝ) : ℂ)) := by fun_prop
      simp_rw [hpt2]
      rw [intervalIntegral.integral_add (hf1cont.intervalIntegrable 0 T)
        (hf2cont.intervalIntegrable 0 T), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    -- The sine part vanishes, by the substitution `u ↦ T - u` and `f`'s evenness/periodicity.
    have hsin0 : (∫ u in (0 : ℝ)..T, f u * Real.sin (2 * Real.pi * (k : ℝ) * u / T)) = 0 := by
      set H : ℝ → ℝ := fun u => f u * Real.sin (2 * Real.pi * (k : ℝ) * u / T) with hHdef
      have hHodd : ∀ u : ℝ, H (T - u) = -H u := by
        intro u
        have hfeq : f (T - u) = f u := by
          rw [show T - u = -u + T from by ring, hf_periodic (-u), hf_even u]
        have hsineq : Real.sin (2 * Real.pi * (k : ℝ) * (T - u) / T)
            = - Real.sin (2 * Real.pi * (k : ℝ) * u / T) := by
          rw [show 2 * Real.pi * (k : ℝ) * (T - u) / T
              = (k : ℝ) * (2 * Real.pi) - (2 * Real.pi * (k : ℝ) * u / T) from by
            field_simp [hTne]]
          exact Real.sin_int_mul_two_pi_sub _ k
        simp only [hHdef, hfeq, hsineq]
        ring
      have hstep : (∫ u in (0 : ℝ)..T, H (T - u)) = ∫ u in (0 : ℝ)..T, H u := by
        rw [intervalIntegral.integral_comp_sub_left H T]
        norm_num
      have hneg : (∫ u in (0 : ℝ)..T, H (T - u)) = -(∫ u in (0 : ℝ)..T, H u) := by
        simp_rw [hHodd]
        exact intervalIntegral.integral_neg
      rw [hstep] at hneg
      linarith [hneg]
    have hcos_eq : (∫ u in (0 : ℝ)..T, f u * Real.cos (2 * Real.pi * (k : ℝ) * u / T))
        = T * α k := by
      rw [hα k]
      field_simp
    have hFval : (∫ u in (0 : ℝ)..T, F u) = ((T * α k : ℝ) : ℂ) := by
      rw [hFsplit, hsin0, hcos_eq]
      push_cast
      ring
    have hdouble_eq : (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
        (starRingEnd ℂ) (φ x) * φ y * (f (x - y) : ℂ))
        = ((T * T * α k : ℝ) : ℂ) := by
      rw [hdouble, hFval]
      push_cast
      ring
    have hre : 0 ≤ T * T * α k := by
      have := hext.2
      rw [hdouble_eq] at this
      simpa using this
    nlinarith [mul_pos hT hT]
  refine ⟨hnonneg, ?_⟩
  -- **Part 2: the coefficients sum to `f 0 = 1`.**
  have hfejer := fejer_cesaro_mean_periodic_at_zero f T hT hf_cont hf_periodic α hα
  rw [hf0] at hfejer
  set a : ℕ → ℝ := fun n => ∑ k ∈ Finset.Icc (-(n : ℤ)) n, α k with hadef
  have hanonneg : ∀ n : ℕ, 0 ≤ a n := fun n => Finset.sum_nonneg (fun i _ => hnonneg i)
  have hmono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro n
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have hsub : Finset.Icc (-(n : ℤ)) (n : ℤ) ⊆ Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1) := by
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
    simpa [hadef, hcast] using this
  have hcesaro : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ n ∈ Finset.range (N + 1), a n)
      atTop (nhds 1) := hfejer
  -- `a` is bounded above by `1`: a short Tauberian argument using the ratio
  -- `(N - m + 1)/(N + 1) → 1`.
  have hbound : ∀ m : ℕ, a m ≤ 1 := by
    intro m
    have hratio0 : Tendsto (fun N : ℕ => ((1 : ℝ) - m + 1 * N) / (1 + 1 * N)) atTop (nhds (1 / 1)) :=
      tendsto_add_mul_div_add_mul_atTop_nhds (1 - (m : ℝ)) 1 1 one_ne_zero
    have hratio : Tendsto (fun N : ℕ => ((N : ℝ) - m + 1) / ((N : ℝ) + 1)) atTop (nhds 1) := by
      have heq : (fun N : ℕ => ((1 : ℝ) - m + 1 * N) / (1 + 1 * N))
          = fun N : ℕ => ((N : ℝ) - m + 1) / ((N : ℝ) + 1) := by
        funext N; ring_nf
      rwa [heq, show (1 : ℝ) / 1 = 1 from by norm_num] at hratio0
    have hkey : ∀ᶠ N : ℕ in atTop, ((N : ℝ) - m + 1) / ((N : ℝ) + 1) * a m
        ≤ (1 / ((N : ℝ) + 1)) * ∑ n ∈ Finset.range (N + 1), a n := by
      filter_upwards [eventually_ge_atTop m] with N hmN
      have hsub2 : Finset.Ico m (N + 1) ⊆ Finset.range (N + 1) := by
        intro x hx
        simp only [Finset.mem_Ico] at hx
        simp only [Finset.mem_range]
        omega
      have hpointwise : ∀ n ∈ Finset.Ico m (N + 1), a m ≤ a n := fun n hn =>
        hmono (Finset.mem_Ico.mp hn).1
      have hstep1 : ((N + 1 - m : ℕ) : ℝ) * a m ≤ ∑ n ∈ Finset.Ico m (N + 1), a n := by
        calc ((N + 1 - m : ℕ) : ℝ) * a m = ∑ _n ∈ Finset.Ico m (N + 1), a m := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          _ ≤ ∑ n ∈ Finset.Ico m (N + 1), a n := Finset.sum_le_sum hpointwise
      have hstep2 : ∑ n ∈ Finset.Ico m (N + 1), a n ≤ ∑ n ∈ Finset.range (N + 1), a n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => hanonneg i)
      have hcast2 : ((N + 1 - m : ℕ) : ℝ) = (N : ℝ) - m + 1 := by
        have hle : m ≤ N + 1 := by omega
        push_cast [Nat.cast_sub hle]
        ring
      calc ((N : ℝ) - m + 1) / ((N : ℝ) + 1) * a m
          = (1 / ((N : ℝ) + 1)) * (((N + 1 - m : ℕ) : ℝ) * a m) := by rw [hcast2]; ring
        _ ≤ (1 / ((N : ℝ) + 1)) * ∑ n ∈ Finset.Ico m (N + 1), a n :=
            mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ ≤ (1 / ((N : ℝ) + 1)) * ∑ n ∈ Finset.range (N + 1), a n :=
            mul_le_mul_of_nonneg_left hstep2 (by positivity)
    have hlim1 : Tendsto (fun N : ℕ => ((N : ℝ) - m + 1) / ((N : ℝ) + 1) * a m)
        atTop (nhds (1 * a m)) := hratio.mul_const (a m)
    have := le_of_tendsto_of_tendsto hlim1 hcesaro hkey
    simpa using this
  -- Hence `a` converges to `1` (the Cesàro-mean limit).
  have hconv0 : Tendsto a atTop (nhds (⨆ n, a n)) :=
    tendsto_atTop_ciSup hmono ⟨1, fun x ⟨n, hn⟩ => hn ▸ hbound n⟩
  have hcesaro2 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), a n)
      atTop (nhds (⨆ n, a n)) := by
    have h := hconv0.cesaro.comp (tendsto_add_atTop_nat 1)
    have heq : ((fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) ∘ fun N : ℕ => N + 1)
        = fun N : ℕ => ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1), a n := by
      funext N
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    rwa [heq] at h
  have hL_eq : (⨆ n, a n) = 1 := by
    have heq1 : (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ n ∈ Finset.range (N + 1), a n)
        = fun N : ℕ => (((N : ℝ) + 1)⁻¹) * ∑ n ∈ Finset.range (N + 1), a n := by
      funext N; rw [one_div]
    rw [heq1] at hcesaro
    exact tendsto_nhds_unique hcesaro2 hcesaro
  have hconv : Tendsto a atTop (nhds 1) := hL_eq ▸ hconv0
  -- `1` is the least upper bound of all finite partial sums of `α`, hence `HasSum α 1`.
  have hLUB : IsLUB (Set.range fun s : Finset ℤ => ∑ k ∈ s, α k) 1 := by
    constructor
    · rintro x ⟨s, rfl⟩
      by_cases hs : s.Nonempty
      · set n := (s.image Int.natAbs).sup id with hndef
        have hsub : s ⊆ Finset.Icc (-(n : ℤ)) n := by
          intro k hk
          simp only [Finset.mem_Icc]
          have hle : k.natAbs ≤ n := by
            rw [hndef]
            exact Finset.le_sup (f := id) (Finset.mem_image_of_mem Int.natAbs hk)
          omega
        calc ∑ k ∈ s, α k ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n, α k :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
          _ ≤ 1 := hbound n
      · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
    · intro b hb
      have hab : ∀ n, a n ≤ b := fun n => hb ⟨Finset.Icc (-(n : ℤ)) n, rfl⟩
      exact le_of_tendsto' hconv hab
  exact (hasSum_of_isLUB_of_nonneg 1 hnonneg hLUB).tsum_eq

