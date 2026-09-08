import Definitions.Def_DDPM_process
open MeasureTheory Real
open DDPM

/-- Gibbs' inequality on densities: the elementary replacement for Jensen. -/
theorem gibbs {α : Type*} [MeasurableSpace α] {μ : Measure α} (P Q : α → ℝ)
    (hQpos : ∀ y, 0 < Q y) (hPpos : ∀ y, 0 < P y)
    (hQ1 : ∫ y, Q y ∂μ = 1) (hQint : Integrable Q μ) (hPint : Integrable P μ)
    (hlog : Integrable (fun y => Real.log (P y / Q y) * Q y) μ) :
    ∫ y, Real.log (P y / Q y) * Q y ∂μ ≤ Real.log (∫ y, P y ∂μ) := by
  have hμ : μ ≠ 0 := by
    intro h; rw [h] at hQ1; simp at hQ1
  have hZpos : 0 < ∫ y, P y ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun y => (hPpos y).le) hPint]
    have hsupp : Function.support P = Set.univ :=
      Set.eq_univ_of_forall fun y => ne_of_gt (hPpos y)
    rw [hsupp]
    exact Measure.measure_univ_pos.mpr hμ
  set Z : ℝ := ∫ y, P y ∂μ with hZ
  have hsplit : ∀ y, Real.log (P y / Q y) * Q y
      = Real.log (P y / (Z * Q y)) * Q y + Real.log Z * Q y := by
    intro y
    have hq := hQpos y
    have hp := hPpos y
    have h1 : P y / Q y = P y / (Z * Q y) * Z := by field_simp
    rw [h1, Real.log_mul (ne_of_gt (div_pos hp (mul_pos hZpos hq))) (ne_of_gt hZpos)]
    ring
  have hbound : ∀ y, Real.log (P y / (Z * Q y)) * Q y ≤ P y / Z - Q y := by
    intro y
    have hq := hQpos y
    have hr : 0 < P y / (Z * Q y) := div_pos (hPpos y) (mul_pos hZpos hq)
    have hlog1 := Real.log_le_sub_one_of_pos hr
    have hkey : P y / (Z * Q y) * Q y = P y / Z := by field_simp
    nlinarith [hlog1, hq, hkey]
  have hint2 : Integrable (fun y => Real.log (P y / (Z * Q y)) * Q y) μ := by
    have hrw : (fun y => Real.log (P y / (Z * Q y)) * Q y)
        = fun y => Real.log (P y / Q y) * Q y - Real.log Z * Q y := by
      funext y; rw [hsplit y]; ring
    rw [hrw]
    exact hlog.sub (hQint.const_mul _)
  have hint3 : Integrable (fun y => P y / Z - Q y) μ := (hPint.div_const Z).sub hQint
  have hmono := integral_mono hint2 hint3 hbound
  rw [integral_sub (hPint.div_const Z) hQint, integral_div, hQ1, ← hZ,
    div_self (ne_of_gt hZpos), sub_self] at hmono
  calc ∫ y, Real.log (P y / Q y) * Q y ∂μ
      = ∫ y, (Real.log (P y / (Z * Q y)) * Q y + Real.log Z * Q y) ∂μ :=
        integral_congr_ae (ae_of_all _ hsplit)
    _ = (∫ y, Real.log (P y / (Z * Q y)) * Q y ∂μ) + Real.log Z * ∫ y, Q y ∂μ := by
        rw [integral_add hint2 (hQint.const_mul _), integral_const_mul]
    _ ≤ 0 + Real.log Z * 1 := by rw [hQ1]; linarith [hmono]
    _ = Real.log Z := by ring
