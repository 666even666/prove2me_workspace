import Mathlib
import Definitions.Def_IsStationary
import Theorems.Thm_SecondLaw_step_klDiv_le

open MeasureTheory ProbabilityTheory

namespace SecondLaw

/-- **The second law of thermodynamics** (Goal). For a Markov kernel `κ` with stationary
distribution `π`, and any initial distribution `μ`, the Kullback–Leibler divergence to
equilibrium `D(μ_n ‖ π)` — where `μ_n` is the distribution after `n` steps of `κ` — is a
non-increasing function of `n`: the system's statistical distance from equilibrium never
increases under its own dynamics. -/
theorem klDiv_antitone {Ω : Type*} {mΩ : MeasurableSpace Ω} (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (μ π : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure π] (hπ : IsStationary κ π) :
    Antitone (fun n => InformationTheory.klDiv ((κ ∘ₘ ·) ^[n] μ) π) := by
  have hfin : ∀ n, IsFiniteMeasure ((κ ∘ₘ ·) ^[n] μ) := by
    intro n
    induction n with
    | zero => simpa using (inferInstance : IsFiniteMeasure μ)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have := ih
      infer_instance
  apply antitone_nat_of_succ_le
  intro n
  rw [Function.iterate_succ_apply']
  have := hfin n
  exact step_klDiv_le κ ((κ ∘ₘ ·) ^[n] μ) π hπ

end SecondLaw
