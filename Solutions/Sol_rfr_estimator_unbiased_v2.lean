import Mathlib
import Definitions.Def_PositiveDefiniteKernel
import Definitions.Def_RandomFourierRotation
import Theorems.Thm_ClockRoPE_fourierTransform_bochner_inversion

open MeasureTheory Complex
open ClockRoPE

theorem solution
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPositiveDefiniteKernel f) (hf0 : f 0 = 1)
    (n : ℕ) (q k : Fin (2 * n) → ℝ) (pm pn : ℝ) :
    ∫ ξ : Fin n → ℝ, rfrEstimator n q k pm pn ξ
        ∂(Measure.pi fun _ : Fin n =>
            (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (fourierTransform f x))
      = dotProduct q k * f (pm - pn) := by
  have hbochner := fourierTransform_bochner_inversion f hf_cont hf_int hf_pd hf0
  have hτcont := hbochner.1
  have hτnonneg := hbochner.2.1
  have hτint1 := hbochner.2.2.1
  have hinv := hbochner.2.2.2
  set τ : ℝ → ℝ := fourierTransform f with hτdef
  set ν : Measure ℝ := (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (τ x) with hνdef
  set μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => ν with hμdef
  -- τ is integrable: otherwise ∫ τ would be the junk value 0, contradicting ∫ τ = 1.
  have hτ_int : Integrable τ (volume : Measure ℝ) := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hτint1
    norm_num at hτint1
  -- ν is a probability measure.
  have hν_prob : IsProbabilityMeasure ν := by
    constructor
    have h1 : ν Set.univ = ∫⁻ x, ENNReal.ofReal (τ x) ∂(volume : Measure ℝ) := by
      rw [hνdef, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ]
    rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hτ_int
      (Filter.Eventually.of_forall hτnonneg), hτint1, ENNReal.ofReal_one]
  -- μ is a probability measure (a finite product of probability measures).
  have hμ_prob : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  -- Marginal formula: integrating a function of only the `j`-th coordinate against `μ`
  -- is the same as integrating it against `ν`.
  have hmarg : ∀ (j : Fin n) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (g : ℝ → E), AEStronglyMeasurable g ν →
      ∫ ξ : Fin n → ℝ, g (ξ j) ∂μ = ∫ x : ℝ, g x ∂ν := by
    intro j E _ _ g hg
    have hmp : MeasurePreserving (Function.eval j) μ ν :=
      MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => ν) j
    have heq : Measure.map (Function.eval j) μ = ν := hmp.map_eq
    have hg' : AEStronglyMeasurable g (Measure.map (Function.eval j) μ) := by
      rw [heq]; exact hg
    have hmeas : Measurable (Function.eval j : (Fin n → ℝ) → ℝ) := measurable_pi_apply j
    have hstep := MeasureTheory.integral_map hmeas.aemeasurable hg'
    rw [heq] at hstep
    exact hstep.symm
  -- Rewrite the estimator as a finite sum of per-coordinate terms.
  have hrw : ∀ ξ : Fin n → ℝ, rfrEstimator n q k pm pn ξ =
      ∑ j : Fin n,
        dotProduct
          (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pm)) (featurePair n q j))
          (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pn)) (featurePair n k j)) := by
    intro ξ; rfl
  -- The `j`-th term, as a real-valued Complex-algebra identity: the dot product of the two
  -- rotated feature pairs equals the real part of a product of complex exponentials.
  have hpair : ∀ (j : Fin n) (x : ℝ),
      dotProduct
        (Matrix.mulVec (rotation2 (2 * Real.pi * x * pm)) (featurePair n q j))
        (Matrix.mulVec (rotation2 (2 * Real.pi * x * pn)) (featurePair n k j))
      = (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))).re := by
    intro j x
    have hexp : Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))
        = (Real.cos (2 * Real.pi * x * pm - 2 * Real.pi * x * pn) : ℂ)
          + (Real.sin (2 * Real.pi * x * pm - 2 * Real.pi * x * pn) : ℂ) * Complex.I := by
      have hcast : (2 : ℂ) * Real.pi * Complex.I * x * (pm - pn)
          = ((2 * Real.pi * x * pm - 2 * Real.pi * x * pn : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hcast, Complex.exp_ofReal_mul_I]
    rw [hexp, Real.cos_sub, Real.sin_sub]
    simp only [rotation2, Matrix.mulVec, dotProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero,
      zero_add, neg_zero]
    ring
  -- Each per-coordinate term is bounded, hence integrable against the probability measure `μ`.
  -- (Stated with `+ -(...)` rather than `-(...)` to match the shape `simp` produces below.)
  have hbdd : ∀ (a0 a1 b0 b1 θm θn : ℝ),
      |(Real.cos θm * a0 + -Real.sin θm * a1) * (Real.cos θn * b0 + -Real.sin θn * b1)
        + (Real.sin θm * a0 + Real.cos θm * a1) * (Real.sin θn * b0 + Real.cos θn * b1)|
      ≤ 2 * (|a0| + |a1|) * (|b0| + |b1|) := by
    intro a0 a1 b0 b1 θm θn
    have hc1 : |Real.cos θm * a0 + -Real.sin θm * a1| ≤ |a0| + |a1| := by
      have e1 : |Real.cos θm * a0| ≤ |a0| :=
        calc |Real.cos θm * a0| = |Real.cos θm| * |a0| := abs_mul _ _
          _ ≤ 1 * |a0| := by gcongr; exact Real.abs_cos_le_one θm
          _ = |a0| := one_mul _
      have e2 : |(-Real.sin θm) * a1| ≤ |a1| :=
        calc |(-Real.sin θm) * a1| = |Real.sin θm| * |a1| := by rw [abs_mul, abs_neg]
          _ ≤ 1 * |a1| := by gcongr; exact Real.abs_sin_le_one θm
          _ = |a1| := one_mul _
      exact (abs_add_le _ _).trans (add_le_add e1 e2)
    have hc2 : |Real.cos θn * b0 + -Real.sin θn * b1| ≤ |b0| + |b1| := by
      have e1 : |Real.cos θn * b0| ≤ |b0| :=
        calc |Real.cos θn * b0| = |Real.cos θn| * |b0| := abs_mul _ _
          _ ≤ 1 * |b0| := by gcongr; exact Real.abs_cos_le_one θn
          _ = |b0| := one_mul _
      have e2 : |(-Real.sin θn) * b1| ≤ |b1| :=
        calc |(-Real.sin θn) * b1| = |Real.sin θn| * |b1| := by rw [abs_mul, abs_neg]
          _ ≤ 1 * |b1| := by gcongr; exact Real.abs_sin_le_one θn
          _ = |b1| := one_mul _
      exact (abs_add_le _ _).trans (add_le_add e1 e2)
    have hs1 : |Real.sin θm * a0 + Real.cos θm * a1| ≤ |a0| + |a1| := by
      have e1 : |Real.sin θm * a0| ≤ |a0| :=
        calc |Real.sin θm * a0| = |Real.sin θm| * |a0| := abs_mul _ _
          _ ≤ 1 * |a0| := by gcongr; exact Real.abs_sin_le_one θm
          _ = |a0| := one_mul _
      have e2 : |Real.cos θm * a1| ≤ |a1| :=
        calc |Real.cos θm * a1| = |Real.cos θm| * |a1| := abs_mul _ _
          _ ≤ 1 * |a1| := by gcongr; exact Real.abs_cos_le_one θm
          _ = |a1| := one_mul _
      exact (abs_add_le _ _).trans (add_le_add e1 e2)
    have hs2 : |Real.sin θn * b0 + Real.cos θn * b1| ≤ |b0| + |b1| := by
      have e1 : |Real.sin θn * b0| ≤ |b0| :=
        calc |Real.sin θn * b0| = |Real.sin θn| * |b0| := abs_mul _ _
          _ ≤ 1 * |b0| := by gcongr; exact Real.abs_sin_le_one θn
          _ = |b0| := one_mul _
      have e2 : |Real.cos θn * b1| ≤ |b1| :=
        calc |Real.cos θn * b1| = |Real.cos θn| * |b1| := abs_mul _ _
          _ ≤ 1 * |b1| := by gcongr; exact Real.abs_cos_le_one θn
          _ = |b1| := one_mul _
      exact (abs_add_le _ _).trans (add_le_add e1 e2)
    calc |(Real.cos θm * a0 + -Real.sin θm * a1) * (Real.cos θn * b0 + -Real.sin θn * b1)
          + (Real.sin θm * a0 + Real.cos θm * a1) * (Real.sin θn * b0 + Real.cos θn * b1)|
        ≤ |(Real.cos θm * a0 + -Real.sin θm * a1) * (Real.cos θn * b0 + -Real.sin θn * b1)|
          + |(Real.sin θm * a0 + Real.cos θm * a1) * (Real.sin θn * b0 + Real.cos θn * b1)| :=
          abs_add_le _ _
      _ = |Real.cos θm * a0 + -Real.sin θm * a1| * |Real.cos θn * b0 + -Real.sin θn * b1|
          + |Real.sin θm * a0 + Real.cos θm * a1| * |Real.sin θn * b0 + Real.cos θn * b1| := by
          rw [abs_mul, abs_mul]
      _ ≤ (|a0| + |a1|) * (|b0| + |b1|) + (|a0| + |a1|) * (|b0| + |b1|) := by
          gcongr
      _ = 2 * (|a0| + |a1|) * (|b0| + |b1|) := by ring
  have hInt : ∀ j : Fin n, Integrable
      (fun ξ : Fin n → ℝ => dotProduct
        (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pm)) (featurePair n q j))
        (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pn)) (featurePair n k j))) μ := by
    intro j
    apply Integrable.of_mem_Icc
      (-(2 * (|featurePair n q j 0| + |featurePair n q j 1|) *
          (|featurePair n k j 0| + |featurePair n k j 1|)))
      (2 * (|featurePair n q j 0| + |featurePair n q j 1|) *
          (|featurePair n k j 0| + |featurePair n k j 1|))
    · apply Continuous.aemeasurable
      simp only [rotation2, Matrix.mulVec, dotProduct, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
      fun_prop
    · refine Filter.Eventually.of_forall (fun ξ => ?_)
      simp only [rotation2, Matrix.mulVec, dotProduct, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
      exact abs_le.mp (hbdd _ _ _ _ _ _)
  -- Swap sum and integral, then rewrite each term via `hpair`.
  simp_rw [hrw]
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => hInt j)]
  have hstep2 : ∀ j : Fin n,
      (∫ ξ : Fin n → ℝ, dotProduct
        (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pm)) (featurePair n q j))
        (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pn)) (featurePair n k j)) ∂μ)
      = (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          (f (pm - pn) : ℂ)).re := by
    intro j
    have hcongr : (fun ξ : Fin n → ℝ => dotProduct
          (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pm)) (featurePair n q j))
          (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pn)) (featurePair n k j)))
        = fun ξ => (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
            (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
            Complex.exp (2 * Real.pi * Complex.I * (ξ j) * (pm - pn))).re :=
      funext fun ξ => hpair j (ξ j)
    rw [hcongr, hmarg j
      (fun x => (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))).re) (by fun_prop)]
    rw [show ν = (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (τ x) from hνdef]
    have hmeasτ : Measurable fun x : ℝ => ENNReal.ofReal (τ x) :=
      (ENNReal.measurable_ofReal).comp hτcont.measurable
    rw [integral_withDensity_eq_integral_toReal_smul hmeasτ
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have hpt : ∀ x : ℝ, (ENNReal.ofReal (τ x)).toReal •
        (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))).re
      = (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          ((τ x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn)))).re := by
      intro x
      rw [ENNReal.toReal_ofReal (hτnonneg x), smul_eq_mul,
        show (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
            (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
            ((τ x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))))
          = (τ x : ℂ) * (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
            (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
            Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))) from by ring,
        Complex.re_ofReal_mul]
    simp_rw [hpt]
    have hAB_int : Integrable
        (fun x : ℝ => (τ x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn)))
        (volume : Measure ℝ) := by
      apply hτ_int.ofReal.mul_bdd (c := 1)
      · fun_prop
      · refine Filter.Eventually.of_forall fun x => ?_
        rw [show (2 : ℂ) * Real.pi * Complex.I * x * (pm - pn)
            = ((2 * Real.pi * x * (pm - pn) : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I]
    have hF_int : Integrable
        (fun x : ℝ => ((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          ((τ x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))))
        (volume : Measure ℝ) := hAB_int.const_mul _
    show ∫ x : ℝ, RCLike.re
        (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          ((τ x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn))))
        ∂(volume : Measure ℝ)
      = RCLike.re (((featurePair n q j 0 : ℂ) + (featurePair n q j 1 : ℂ) * Complex.I) *
          (starRingEnd ℂ ((featurePair n k j 0 : ℂ) + (featurePair n k j 1 : ℂ) * Complex.I)) *
          (f (pm - pn) : ℂ))
    rw [integral_re hF_int]
    congr 1
    rw [MeasureTheory.integral_const_mul,
      show (fun x : ℝ => (τ x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn)))
          = (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * x * (pm - pn)) * (τ x : ℂ))
        from funext fun x => mul_comm _ _]
    have hinv' := hinv (pm - pn)
    push_cast at hinv'
    rw [← hinv']
  -- Assemble: sum the per-coordinate results and match against `dotProduct q k`.
  simp_rw [hstep2]
  rw [← Complex.re_sum, ← Finset.sum_mul, Complex.re_mul_ofReal]
  congr 1
  rw [Complex.re_sum]
  have hterm : ∀ i : Fin n,
      (((featurePair n q i 0 : ℂ) + (featurePair n q i 1 : ℂ) * Complex.I) *
        (starRingEnd ℂ ((featurePair n k i 0 : ℂ) + (featurePair n k i 1 : ℂ) * Complex.I))).re
      = dotProduct (featurePair n q i) (featurePair n k i) := by
    intro i
    simp only [dotProduct, Fin.sum_univ_two, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
      Complex.neg_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, neg_zero]
    ring
  simp_rw [hterm]
  -- Pairs-splitting: the sum of the `n` pairwise dot products equals the full `2n`-dim dot
  -- product, via the bijection `Fin n × Fin 2 ≃ Fin (2 * n)`, `(j, r) ↦ 2 * j + r`.
  show ∑ i : Fin n, dotProduct (featurePair n q i) (featurePair n k i) = dotProduct q k
  simp only [dotProduct]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Finset.sum_nbij'
    (i := fun p : Fin n × Fin 2 => (⟨2 * p.1.1 + p.2.1, by
      have h1 := p.1.2; have h2 := p.2.2; omega⟩ : Fin (2 * n)))
    (j := fun x : Fin (2 * n) => ((⟨x.1 / 2, by have := x.2; omega⟩ : Fin n),
      (⟨x.1 % 2, by omega⟩ : Fin 2)))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro p _
    have h2 := p.2.2
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [] <;> omega
  · intro x _
    refine Fin.ext ?_
    simp only []
    omega
  · intro p _
    obtain ⟨j, r⟩ := p
    fin_cases r <;> simp [featurePair]
