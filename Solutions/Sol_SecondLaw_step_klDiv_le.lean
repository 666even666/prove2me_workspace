import Mathlib
import Definitions.Def_IsStationary

open MeasureTheory ProbabilityTheory SecondLaw

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (μ π : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure π] (hπ : IsStationary κ π) :
    InformationTheory.klDiv (κ ∘ₘ μ) π ≤ InformationTheory.klDiv μ π := by
  have hπ' : κ ∘ₘ π = π := hπ
  have h := InformationTheory.klDiv_comp_right_le μ π κ
  rwa [hπ'] at h
