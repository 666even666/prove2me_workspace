import Mathlib
import Definitions.Def_PositiveDefiniteKernel
import Definitions.Def_RandomFourierRotation
import Theorems.Thm_ClockRoPE_fourierTransform_bochner_inversion

namespace ClockRoPE

open MeasureTheory Complex

/-- **Proposition 3.1 (Random Fourier Rotation Estimator)** — corrected against
`IsPositiveDefiniteKernel`, superseding `ClockRoPE.rfr_estimator_unbiased`, which used the
under-hypothesized `IsPosDefKernel`.
Let `f : ℝ → ℝ` be a continuous, Lebesgue-integrable, positive-definite kernel with `f 0 = 1`,
and let `τ` be its Fourier transform. For query `q_m ∈ ℝ^{2n}` and key `k_n ∈ ℝ^{2n}` at
positions `p_m, p_n ∈ ℝ`, sample `n` i.i.d. frequencies `ξ_0, …, ξ_{n-1} ∼ τ` and form the
Random Fourier Rotation estimator `ĝ(q_m, k_n, p_m, p_n)` by rotating each feature pair of
`q_m`/`k_n` by the angle `2πξ_j p_m`/`2πξ_j p_n` and summing the pairwise dot products. Then
`ĝ` is an unbiased estimator of `q_m^⊤ k_n · f(p_m - p_n)`. -/
theorem rfr_estimator_unbiased_v2
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
  sorry

end ClockRoPE
