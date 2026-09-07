import Mathlib
import Definitions.Def_PositiveDefiniteKernel
import Definitions.Def_PositiveDefinite
import Theorems.Thm_Bochner_bochner_L1_case

open MeasureTheory
open ClockRoPE

theorem solution
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPositiveDefiniteKernel f) (hf0 : f 0 = 1) :
    Continuous (fourierTransform f) ∧
      (∀ ξ : ℝ, 0 ≤ fourierTransform f ξ) ∧
      (∫ ξ : ℝ, fourierTransform f ξ = 1) ∧
      (∀ x : ℝ, (f x : ℂ) =
        ∫ ξ : ℝ, Complex.exp (2 * Real.pi * Complex.I * ξ * x) * (fourierTransform f ξ : ℂ)) := by
  set g : ℝ → ℂ := fun x => (f x : ℂ) with hgdef
  have hg_cont : Continuous g := Complex.continuous_ofReal.comp hf_cont
  have hg_int : Integrable g (volume : Measure ℝ) := hf_int.ofReal
  have hg_pd : Bochner.IsPositiveDefinite g := hf_pd
  have hg0 : g 0 = 1 := by simp [hgdef, hf0]
  have hfeq : fourierTransform f = Bochner.fourierTransform g := rfl
  have hb := Bochner.bochner_L1_case g hg_cont hg_int hg_pd hg0
  rw [hfeq]
  exact hb
