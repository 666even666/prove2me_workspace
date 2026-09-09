import Mathlib
import Definitions.Def_IsStationary

open MeasureTheory ProbabilityTheory

namespace SecondLaw

/-- **One-step contraction to equilibrium.** A single step of a Markov kernel `κ` never increases
the Kullback–Leibler divergence to a stationary distribution `π`: `D(κ ∘ₘ μ ‖ π) ≤ D(μ ‖ π)`. This
specializes Mathlib's Data Processing Inequality for `klDiv` (`InformationTheory.klDiv_comp_right_le`)
to the case where one of the two measures is `κ`'s own stationary distribution. -/
theorem step_klDiv_le {Ω : Type*} {mΩ : MeasurableSpace Ω} (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (μ π : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure π] (hπ : IsStationary κ π) :
    InformationTheory.klDiv (κ ∘ₘ μ) π ≤ InformationTheory.klDiv μ π := by
  have hπ' : κ ∘ₘ π = π := hπ
  have h := InformationTheory.klDiv_comp_right_le μ π κ
  rwa [hπ'] at h

end SecondLaw
