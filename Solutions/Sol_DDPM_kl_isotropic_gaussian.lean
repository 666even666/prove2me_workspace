import Definitions.Def_DDPM_process
open MeasureTheory Real ProbabilityTheory WithLp
open DDPM

theorem solution {d : ℕ} (m1 m2 : Space d) (v1 v2 : ℝ) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    klPDF (gaussPDF m1 v1) (gaussPDF m2 v2)
      = ‖m1 - m2‖ ^ 2 / (2 * v2) + (d : ℝ) / 2 * (v1 / v2 - 1 - Real.log (v1 / v2)) := by
  ---- coordinates and transfer to the product space
  have coord : ∀ x : Space d, ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    intro x; rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [sq_abs]
  have chg : ∀ g : Space d → ℝ, ∫ x : Space d, g x = ∫ y : Fin d → ℝ, g (toLp 2 y) := fun g =>
    ((PiLp.volume_preserving_toLp (Fin d)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding g).symm
  have chgI : ∀ g : Space d → ℝ,
      Integrable (fun y : Fin d → ℝ => g (toLp 2 y)) ↔ Integrable g := fun g =>
    (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  ---- the isotropic density factorizes over coordinates
  have factor : ∀ (m : Space d) (v : ℝ), 0 < v → ∀ y : Fin d → ℝ,
      gaussPDF m v (toLp 2 y) = ∏ i, gaussianPDFReal (m i) v.toNNReal (y i) := by
    intro m v hv y
    have hvc : ((v.toNNReal : NNReal) : ℝ) = v := Real.coe_toNNReal v hv.le
    have hpos : (0:ℝ) < 2 * π * v := by positivity
    simp only [gaussianPDFReal, hvc, gaussPDF]
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
    congr 1
    · simp only [Finset.card_univ, Fintype.card_fin]
      rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 * π * v) ^ ((1:ℝ)/2)) d,
        ← Real.rpow_mul hpos.le, ← Real.rpow_neg hpos.le]
      congr 1; ring
    · rw [coord, ← Finset.sum_div, ← Finset.sum_neg_distrib]
      congr 1
  ---- one-dimensional moments
  have mom1D : ∀ (μ c : ℝ) (v : NNReal), v ≠ 0 →
      ∫ t, gaussianPDFReal μ v t * (t - c) ^ 2 = (v : ℝ) + (μ - c) ^ 2 := by
    intro μ c v hv
    have hmem2 : MemLp (fun x : ℝ => x) 2 (gaussianReal μ v) :=
      IsGaussian.memLp_id (gaussianReal μ v) 2 (by norm_num)
    have hint2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal μ v) :=
      (memLp_two_iff_integrable_sq hmem2.aestronglyMeasurable).mp hmem2
    have hint1 : Integrable (fun x : ℝ => x) (gaussianReal μ v) := hmem2.integrable (by norm_num)
    have hintsub : Integrable (fun x : ℝ => x - μ) (gaussianReal μ v) :=
      hint1.sub (integrable_const μ)
    have hintsq : Integrable (fun x : ℝ => (x - μ) ^ 2) (gaussianReal μ v) := by
      have h : (fun x : ℝ => (x - μ) ^ 2) = fun x : ℝ => x ^ 2 - 2 * μ * x + μ ^ 2 := by
        funext x; ring
      rw [h]
      exact (hint2.sub (hint1.const_mul (2 * μ))).add (integrable_const _)
    have h2 : ∫ x, (x - μ) ^ 2 ∂(gaussianReal μ v) = (v : ℝ) := by
      have h := variance_eq_integral (X := fun x : ℝ => x) (μ := gaussianReal μ v) (by fun_prop)
      rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
      exact h.symm
    have h1 : ∫ x, (x - μ) ∂(gaussianReal μ v) = 0 := by
      rw [integral_sub hint1 (integrable_const μ), integral_id_gaussianReal, integral_const]
      simp
    have key : ∫ x, (x - c) ^ 2 ∂(gaussianReal μ v) = (v : ℝ) + (μ - c) ^ 2 := by
      have hrw : (fun x : ℝ => (x - c) ^ 2)
          = fun x : ℝ => ((x - μ) ^ 2 + 2 * (μ - c) * (x - μ)) + (μ - c) ^ 2 := by
        funext x; ring
      have hB : Integrable (fun x : ℝ => 2 * (μ - c) * (x - μ)) (gaussianReal μ v) :=
        hintsub.const_mul (2 * (μ - c))
      have hA : Integrable (fun x : ℝ => (x - μ) ^ 2 + 2 * (μ - c) * (x - μ))
          (gaussianReal μ v) := hintsq.add hB
      rw [hrw, integral_add hA (integrable_const _), integral_add hintsq hB,
        integral_const_mul, h2, h1, integral_const]
      simp
    rw [← key, integral_gaussianReal_eq_integral_smul hv]
    simp [smul_eq_mul]
  have int1D : ∀ (μ c : ℝ) (v : NNReal),
      Integrable (fun t : ℝ => gaussianPDFReal μ v t * (t - c) ^ 2) := by
    intro μ c v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [gaussianPDFReal_zero_var]
    have hvpos : (0:ℝ) < (v:ℝ) := lt_of_le_of_ne v.coe_nonneg (by simpa [eq_comm] using hv)
    have hb : (0:ℝ) < 1 / (2 * v) := by positivity
    have base : Integrable (fun u : ℝ => Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2)) :=
      integrable_exp_neg_mul_sq hb
    have lin : Integrable (fun u : ℝ => u * Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2)) :=
      integrable_mul_exp_neg_mul_sq hb
    have quad : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2)) := by
      simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 2)
    have shifted : Integrable (fun u : ℝ =>
        Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2) * (u + (μ - c)) ^ 2) := by
      have hrw : (fun u : ℝ => Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2) * (u + (μ - c)) ^ 2)
          = fun u : ℝ => (u ^ 2 * Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2)
              + (2 * (μ - c)) * (u * Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2)))
              + (μ - c) ^ 2 * Real.exp (-(1 / (2 * (v:ℝ))) * u ^ 2) := by
        funext u; ring
      rw [hrw]
      exact (quad.add (lin.const_mul _)).add (base.const_mul _)
    have h := (shifted.comp_sub_right μ).const_mul (√(2 * π * (v:ℝ)))⁻¹
    refine h.congr ?_
    filter_upwards with t
    simp only [gaussianPDFReal]
    have h1 : -(1 / (2 * (v:ℝ))) * (t - μ) ^ 2 = -(t - μ) ^ 2 / (2 * (v:ℝ)) := by ring
    have h2 : t - μ + (μ - c) = t - c := by ring
    rw [h1, h2]
    ring
  ---- d-dimensional normalization, second moment, and integrability
  have hne : ∀ v : ℝ, 0 < v → v.toNNReal ≠ 0 := by
    intro v hv
    rw [ne_eq, Real.toNNReal_eq_zero]
    exact not_le.mpr hv
  have normD : ∀ (m : Space d) (v : ℝ), 0 < v → ∫ x : Space d, gaussPDF m v x = 1 := by
    intro m v hv
    rw [chg]
    simp_rw [factor m v hv]
    rw [integral_fintype_prod_volume_eq_prod fun i => gaussianPDFReal (m i) v.toNNReal]
    simp [integral_gaussianPDFReal_eq_one _ (hne v hv)]
  have intD_pdf : ∀ (m : Space d) (v : ℝ), 0 < v → Integrable (gaussPDF m v) := by
    intro m v hv
    rw [← chgI]
    simp_rw [factor m v hv, volume_pi]
    exact Integrable.fintype_prod fun i => integrable_gaussianPDFReal (m i) v.toNNReal
  have splitD : ∀ (m m' : Space d) (v : ℝ), 0 < v → ∀ y : Fin d → ℝ,
      gaussPDF m v (toLp 2 y) * ‖(toLp 2 y : Space d) - m'‖ ^ 2
        = ∑ j, ∏ i, (if i = j then gaussianPDFReal (m i) v.toNNReal (y i) * (y i - m' i) ^ 2
            else gaussianPDFReal (m i) v.toNNReal (y i)) := by
    intro m m' v hv y
    rw [factor m v hv, coord, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hite : ∀ i : Fin d,
        (if i = j then gaussianPDFReal (m i) v.toNNReal (y i) * (y i - m' i) ^ 2
          else gaussianPDFReal (m i) v.toNNReal (y i))
        = gaussianPDFReal (m i) v.toNNReal (y i) * (if i = j then (y i - m' i) ^ 2 else 1) := by
      intro i; by_cases h : i = j <;> simp [h]
    rw [Finset.prod_congr rfl fun i _ => hite i, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ j fun i => (y i - m' i) ^ 2]
    simp
  have momD : ∀ (m m' : Space d) (v : ℝ), 0 < v →
      ∫ x : Space d, gaussPDF m v x * ‖x - m'‖ ^ 2 = (d : ℝ) * v + ‖m - m'‖ ^ 2 := by
    intro m m' v hv
    rw [chg]
    simp_rw [splitD m m' v hv]
    have hprodint : ∀ j : Fin d, Integrable (fun y : Fin d → ℝ =>
        ∏ i, (if i = j then gaussianPDFReal (m i) v.toNNReal (y i) * (y i - m' i) ^ 2
          else gaussianPDFReal (m i) v.toNNReal (y i))) := by
      intro j
      rw [volume_pi]
      refine Integrable.fintype_prod (μ := fun _ => volume) (f := fun i t =>
        if i = j then gaussianPDFReal (m i) v.toNNReal t * (t - m' i) ^ 2
        else gaussianPDFReal (m i) v.toNNReal t) fun i => ?_
      by_cases h : i = j
      · subst h
        simp only [eq_self_iff_true, ite_true]
        exact int1D (m i) (m' i) v.toNNReal
      · simp only [if_neg h]
        exact integrable_gaussianPDFReal (m i) v.toNNReal
    rw [integral_finsetSum _ fun j _ => hprodint j]
    have hterm : ∀ j : Fin d,
        ∫ y : Fin d → ℝ, ∏ i, (if i = j then gaussianPDFReal (m i) v.toNNReal (y i)
            * (y i - m' i) ^ 2 else gaussianPDFReal (m i) v.toNNReal (y i))
          = v + (m j - m' j) ^ 2 := by
      intro j
      rw [integral_fintype_prod_volume_eq_prod fun i => fun t =>
        (if i = j then gaussianPDFReal (m i) v.toNNReal t * (t - m' i) ^ 2
          else gaussianPDFReal (m i) v.toNNReal t)]
      have hi : ∀ i : Fin d, (∫ t, (if i = j then gaussianPDFReal (m i) v.toNNReal t
          * (t - m' i) ^ 2 else gaussianPDFReal (m i) v.toNNReal t))
          = if i = j then ((v.toNNReal : ℝ) + (m i - m' i) ^ 2) else 1 := by
        intro i
        by_cases h : i = j
        · subst h
          simp only [eq_self_iff_true, ite_true]
          exact mom1D (m i) (m' i) v.toNNReal (hne v hv)
        · simp only [if_neg h]
          exact integral_gaussianPDFReal_eq_one _ (hne v hv)
      rw [Finset.prod_congr rfl fun i _ => hi i,
        Finset.prod_ite_eq' Finset.univ j fun i => ((v.toNNReal : ℝ) + (m i - m' i) ^ 2)]
      simp [Real.coe_toNNReal v hv.le]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_const,
      coord (m - m')]
    simp
  have intD_mom : ∀ (m m' : Space d) (v : ℝ), 0 < v →
      Integrable (fun x : Space d => gaussPDF m v x * ‖x - m'‖ ^ 2) := by
    intro m m' v hv
    rw [← chgI]
    simp_rw [splitD m m' v hv]
    refine integrable_finsetSum _ fun j _ => ?_
    rw [volume_pi]
    refine Integrable.fintype_prod (μ := fun _ => volume) (f := fun i t =>
      if i = j then gaussianPDFReal (m i) v.toNNReal t * (t - m' i) ^ 2
      else gaussianPDFReal (m i) v.toNNReal t) fun i => ?_
    by_cases h : i = j
    · subst h
      simp only [eq_self_iff_true, ite_true]
      exact int1D (m i) (m' i) v.toNNReal
    · simp only [if_neg h]
      exact integrable_gaussianPDFReal (m i) v.toNNReal
  ---- the logarithm of the ratio
  have hgp : ∀ (m : Space d) (v : ℝ), 0 < v → ∀ x : Space d, 0 < gaussPDF m v x := by
    intro m v hv x
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  have hlogpdf : ∀ (m : Space d) (v : ℝ), 0 < v → ∀ x : Space d,
      Real.log (gaussPDF m v x) = -((d:ℝ)/2) * Real.log (2 * π * v) - ‖x - m‖ ^ 2 / (2 * v) := by
    intro m v hv x
    unfold gaussPDF
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)) (Real.exp_ne_zero _),
      Real.log_rpow (by positivity), Real.log_exp]
    ring
  have hlog : ∀ x : Space d,
      gaussPDF m1 v1 x * Real.log (gaussPDF m1 v1 x / gaussPDF m2 v2 x)
        = (-((d:ℝ)/2) * Real.log (v1 / v2)) * gaussPDF m1 v1 x
          + (-(1 / (2 * v1))) * (gaussPDF m1 v1 x * ‖x - m1‖ ^ 2)
          + (1 / (2 * v2)) * (gaussPDF m1 v1 x * ‖x - m2‖ ^ 2) := by
    intro x
    rw [Real.log_div (ne_of_gt (hgp m1 v1 hv1 x)) (ne_of_gt (hgp m2 v2 hv2 x)),
      hlogpdf m1 v1 hv1, hlogpdf m2 v2 hv2, Real.log_div (ne_of_gt hv1) (ne_of_gt hv2),
      Real.log_mul (by positivity) (ne_of_gt hv1), Real.log_mul (by positivity) (ne_of_gt hv2)]
    ring
  ---- assemble
  unfold klPDF
  simp_rw [hlog]
  have hI1 : Integrable (fun x : Space d =>
      (-((d:ℝ)/2) * Real.log (v1 / v2)) * gaussPDF m1 v1 x) := (intD_pdf m1 v1 hv1).const_mul _
  have hI2 : Integrable (fun x : Space d =>
      (-(1 / (2 * v1))) * (gaussPDF m1 v1 x * ‖x - m1‖ ^ 2)) :=
    (intD_mom m1 m1 v1 hv1).const_mul _
  have hI3 : Integrable (fun x : Space d =>
      (1 / (2 * v2)) * (gaussPDF m1 v1 x * ‖x - m2‖ ^ 2)) := (intD_mom m1 m2 v1 hv1).const_mul _
  have hI12 : Integrable (fun x : Space d =>
      (-((d:ℝ)/2) * Real.log (v1 / v2)) * gaussPDF m1 v1 x
        + (-(1 / (2 * v1))) * (gaussPDF m1 v1 x * ‖x - m1‖ ^ 2)) := hI1.add hI2
  rw [integral_add hI12 hI3, integral_add hI1 hI2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    normD m1 v1 hv1, momD m1 m1 v1 hv1, momD m1 m2 v1 hv1]
  simp only [sub_self, norm_zero]
  field_simp
  ring
