import Mathlib
import Definitions.Def_PositiveDefiniteKernel
import Definitions.Def_RandomFourierRotation
import Theorems.Thm_ClockRoPE_fourierTransform_bochner_inversion
import Theorems.Thm_ClockRoPE_rfr_estimator_unbiased_v2

open MeasureTheory ProbabilityTheory
open scoped NNReal
open ClockRoPE

theorem solution
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPositiveDefiniteKernel f) (hf0 : f 0 = 1)
    (n : ℕ) (q k : Fin (2 * n) → ℝ) (pm pn : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin n =>
        (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (fourierTransform f x))
        {ξ : Fin n → ℝ |
          ε ≤ |(1 / (n : ℝ)) * rfrEstimator n q k pm pn ξ
                - (1 / (n : ℝ)) * (dotProduct q k * f (pm - pn))|}
      ≤ ENNReal.ofReal
          (2 * Real.exp (-(ε ^ 2 * (2 * (n : ℝ)) ^ 2 /
            (8 * ∑ j : Fin n,
              (pairNorm (featurePair n q j) * pairNorm (featurePair n k j)) ^ 2)))) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: the averaged estimator's defining condition is vacuous (`1 / 0 = 0` in Lean),
    -- so the event set is empty and the bound is trivial.
    subst hn0
    have hempty : {ξ : Fin 0 → ℝ |
        ε ≤ |(1 / ((0 : ℕ) : ℝ)) * rfrEstimator 0 q k pm pn ξ
              - (1 / ((0 : ℕ) : ℝ)) * (dotProduct q k * f (pm - pn))|} = ∅ := by
      ext ξ
      simp only [Nat.cast_zero, div_zero, zero_mul, sub_zero, abs_zero, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      linarith
    rw [hempty]
    simp
  -- `n > 0` from here on.
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hbochner := fourierTransform_bochner_inversion f hf_cont hf_int hf_pd hf0
  have hτcont := hbochner.1
  have hτnonneg := hbochner.2.1
  have hτint1 := hbochner.2.2.1
  set τ : ℝ → ℝ := fourierTransform f with hτdef
  set ν : Measure ℝ := (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (τ x) with hνdef
  set μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => ν with hμdef
  have hτ_int : Integrable τ (volume : Measure ℝ) := by
    by_contra h
    rw [MeasureTheory.integral_undef h] at hτint1
    norm_num at hτint1
  have hν_prob : IsProbabilityMeasure ν := by
    constructor
    have h1 : ν Set.univ = ∫⁻ x, ENNReal.ofReal (τ x) ∂(volume : Measure ℝ) := by
      rw [hνdef, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h1, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hτ_int
      (Filter.Eventually.of_forall hτnonneg), hτint1, ENNReal.ofReal_one]
  have hμ_prob : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  have hmean := rfr_estimator_unbiased_v2 f hf_cont hf_int hf_pd hf0 n q k pm pn
  rw [← hνdef, ← hμdef] at hmean
  -- The `j`-th raw (uncentered) term of the estimator, as a function of a single frequency.
  set X : Fin n → ℝ → ℝ := fun j x =>
    dotProduct (Matrix.mulVec (rotation2 (2 * Real.pi * x * pm)) (featurePair n q j))
      (Matrix.mulVec (rotation2 (2 * Real.pi * x * pn)) (featurePair n k j)) with hXdef
  have hrw : rfrEstimator n q k pm pn = fun ξ : Fin n → ℝ => ∑ j, X j (ξ j) := rfl
  -- Each rotation preserves the Euclidean norm of a feature pair.
  have hrot_norm : ∀ (θ : ℝ) (v : Fin 2 → ℝ),
      pairNorm (Matrix.mulVec (rotation2 θ) v) = pairNorm v := by
    intro θ v
    simp only [pairNorm, rotation2, Matrix.mulVec, dotProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq θ]
  -- Tight 2D Cauchy-Schwarz bound.
  have hcs2d : ∀ (v w : Fin 2 → ℝ), |dotProduct v w| ≤ pairNorm v * pairNorm w := by
    intro v w
    simp only [pairNorm, dotProduct, Fin.sum_univ_two]
    have hkey : (v 0 * w 0 + v 1 * w 1) ^ 2 ≤ (v 0 ^ 2 + v 1 ^ 2) * (w 0 ^ 2 + w 1 ^ 2) := by
      nlinarith [sq_nonneg (v 0 * w 1 - v 1 * w 0)]
    calc |v 0 * w 0 + v 1 * w 1| = Real.sqrt ((v 0 * w 0 + v 1 * w 1) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((v 0 ^ 2 + v 1 ^ 2) * (w 0 ^ 2 + w 1 ^ 2)) := Real.sqrt_le_sqrt hkey
      _ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) * Real.sqrt (w 0 ^ 2 + w 1 ^ 2) :=
          Real.sqrt_mul (by positivity) _
  -- The `j`-th term's bounding range: `M j = ‖q_m^{(j)}‖ ‖k_n^{(j)}‖`.
  set M : Fin n → ℝ := fun j => pairNorm (featurePair n q j) * pairNorm (featurePair n k j)
    with hMdef
  have hM_nonneg : ∀ j, 0 ≤ M j := fun j => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hMbound : ∀ (j : Fin n) (x : ℝ), X j x ∈ Set.Icc (-(M j)) (M j) := by
    intro j x
    have hcs : |X j x| ≤ M j := by
      calc |X j x|
          ≤ pairNorm (Matrix.mulVec (rotation2 (2 * Real.pi * x * pm)) (featurePair n q j))
              * pairNorm (Matrix.mulVec (rotation2 (2 * Real.pi * x * pn)) (featurePair n k j)) :=
            hcs2d _ _
        _ = M j := by rw [hrot_norm, hrot_norm]
    exact abs_le.mp hcs
  -- Continuity and measurability of each raw term.
  have hXcont : ∀ j, Continuous (X j) := by
    intro j
    simp only [hXdef, rotation2, Matrix.mulVec, dotProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    fun_prop
  have hXmeas : ∀ j, Measurable (X j) := fun j => (hXcont j).measurable
  have hcompmeas : ∀ j, Measurable (fun ξ : Fin n → ℝ => X j (ξ j)) :=
    fun j => (hXmeas j).comp (measurable_pi_apply j)
  -- Integrability of each raw term against `μ`, from the bound above.
  have hInt : ∀ j : Fin n, Integrable (fun ξ : Fin n → ℝ => X j (ξ j)) μ := by
    intro j
    exact Integrable.of_mem_Icc (-(M j)) (M j) (hcompmeas j).aemeasurable
      (Filter.Eventually.of_forall fun ξ => hMbound j (ξ j))
  -- The centering constants sum to the mean identity of Proposition 3.1.
  set c : Fin n → ℝ := fun j => μ[fun ξ => X j (ξ j)] with hcdef
  have hsum_eq : ∑ j, c j = dotProduct q k * f (pm - pn) := by
    have hstep : μ[rfrEstimator n q k pm pn] = ∑ j, c j := by
      rw [hrw, MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hInt j)]
    rw [← hstep]
    exact hmean
  -- Independence of the coordinate projections under the product measure.
  have hindep0 : iIndepFun (fun j (ξ : Fin n → ℝ) => X j (ξ j)) μ :=
    iIndepFun_pi (fun j => (hXmeas j).aemeasurable)
  -- The bounding constants, as `ℝ≥0` (`HasSubgaussianMGF`'s parameter is `ℝ≥0`).
  set Mnn : Fin n → ℝ≥0 := fun j => (M j).toNNReal with hMnndef
  have hMnn_coe : ∀ j, ((Mnn j : ℝ≥0) : ℝ) = M j := fun j => Real.coe_toNNReal _ (hM_nonneg j)
  -- Each centered term is sub-Gaussian, by Hoeffding's lemma for bounded random variables.
  have hsubG : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ξ : Fin n → ℝ => X j (ξ j) - c j) (Mnn j ^ 2) μ := by
    intro j _
    have hb : ∀ᵐ ξ ∂μ, X j (ξ j) ∈ Set.Icc (-(M j)) (M j) :=
      Filter.Eventually.of_forall (fun ξ => hMbound j (ξ j))
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ξ : Fin n → ℝ => X j (ξ j))
      (hcompmeas j).aemeasurable hb
    have hMM : (‖(M j) - (-(M j))‖₊ / 2) ^ 2 = Mnn j ^ 2 := by
      rw [← NNReal.coe_inj]
      push_cast
      rw [Real.norm_eq_abs, show (M j) - (-(M j)) = 2 * M j from by ring,
        abs_of_nonneg (by linarith [hM_nonneg j] : (0:ℝ) ≤ 2 * M j), hMnn_coe]
      ring
    rwa [hMM] at h
  have hsub : iIndepFun (fun j (ξ : Fin n → ℝ) => X j (ξ j) - c j) μ :=
    hindep0.comp (g := fun j (x : ℝ) => x - c j) (fun j => by fun_prop)
  -- One-sided Hoeffding bound, and its mirror image for the negated sum.
  have hone := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hsub hsubG
    (show (0:ℝ) ≤ ε * n by positivity)
  have hnegsubG : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ξ : Fin n → ℝ => -(X j (ξ j) - c j)) (Mnn j ^ 2) μ :=
    fun j hj => (hsubG j hj).neg
  have hnegsub : iIndepFun (fun j (ξ : Fin n → ℝ) => -(X j (ξ j) - c j)) μ :=
    hsub.comp (g := fun (_ : Fin n) (x : ℝ) => -x) (fun _ => by fun_prop)
  have htwo := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hnegsub hnegsubG
    (show (0:ℝ) ≤ ε * n by positivity)
  simp only [NNReal.coe_sum, NNReal.coe_pow, hMnn_coe] at hone htwo
  -- Union bound for the two-sided event.
  have hsub2 : {ξ : Fin n → ℝ | ε * n ≤ |∑ j, (X j (ξ j) - c j)|}
      ⊆ {ξ | ε * n ≤ ∑ j, (X j (ξ j) - c j)} ∪ {ξ | ε * n ≤ ∑ j, -(X j (ξ j) - c j)} := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib] at hξ ⊢
    rcases abs_choice (∑ j, (X j (ξ j) - c j)) with h | h
    · rw [h] at hξ; exact Or.inl hξ
    · rw [h] at hξ; exact Or.inr hξ
  have hboth : μ.real {ξ : Fin n → ℝ | ε * n ≤ |∑ j, (X j (ξ j) - c j)|}
      ≤ 2 * Real.exp (-(ε * n) ^ 2 / (2 * ∑ j, (M j) ^ 2)) := by
    calc μ.real {ξ : Fin n → ℝ | ε * n ≤ |∑ j, (X j (ξ j) - c j)|}
        ≤ μ.real ({ξ | ε * n ≤ ∑ j, (X j (ξ j) - c j)}
            ∪ {ξ | ε * n ≤ ∑ j, -(X j (ξ j) - c j)}) :=
          measureReal_mono hsub2
      _ ≤ μ.real {ξ | ε * n ≤ ∑ j, (X j (ξ j) - c j)}
          + μ.real {ξ | ε * n ≤ ∑ j, -(X j (ξ j) - c j)} := measureReal_union_le _ _
      _ ≤ Real.exp (-(ε * n) ^ 2 / (2 * ∑ j, (M j) ^ 2))
          + Real.exp (-(ε * n) ^ 2 / (2 * ∑ j, (M j) ^ 2)) := add_le_add hone htwo
      _ = 2 * Real.exp (-(ε * n) ^ 2 / (2 * ∑ j, (M j) ^ 2)) := by ring
  -- Rewrite the target event set to match `hboth`'s event, then convert to `ENNReal`.
  have hset_eq : {ξ : Fin n → ℝ |
      ε ≤ |(1 / (n : ℝ)) * rfrEstimator n q k pm pn ξ - (1 / (n : ℝ)) * (dotProduct q k * f (pm - pn))|}
    = {ξ : Fin n → ℝ | ε * n ≤ |∑ j, (X j (ξ j) - c j)|} := by
    ext ξ
    have heq2 : (1 / (n : ℝ)) * rfrEstimator n q k pm pn ξ
        - (1 / (n : ℝ)) * (dotProduct q k * f (pm - pn))
        = (1 / (n : ℝ)) * (∑ j, (X j (ξ j) - c j)) := by
      rw [hrw, ← hsum_eq, Finset.sum_sub_distrib, mul_sub]
    simp only [Set.mem_setOf_eq, heq2, abs_mul,
      abs_of_pos (show (0:ℝ) < 1 / (n : ℝ) by positivity)]
    rw [show (1 / (n : ℝ)) * |∑ j, (X j (ξ j) - c j)| = |∑ j, (X j (ξ j) - c j)| / n from by ring]
    exact le_div_iff₀ hnR
  rw [hset_eq]
  have hfinal : μ.real {ξ : Fin n → ℝ | ε * n ≤ |∑ j, (X j (ξ j) - c j)|}
      ≤ 2 * Real.exp (-(ε ^ 2 * (2 * (n : ℝ)) ^ 2 / (8 * ∑ j, (M j) ^ 2))) := by
    refine hboth.trans_eq ?_
    congr 2
    field_simp
    ring
  calc μ {ξ : Fin n → ℝ | ε * n ≤ |∑ j, (X j (ξ j) - c j)|}
      = ENNReal.ofReal (μ.real {ξ : Fin n → ℝ | ε * n ≤ |∑ j, (X j (ξ j) - c j)|}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * (2 * (n : ℝ)) ^ 2 / (8 * ∑ j, (M j) ^ 2)))) :=
        ENNReal.ofReal_le_ofReal hfinal
