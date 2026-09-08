import Mathlib

open MeasureTheory ProbabilityTheory

namespace SecondLaw

/-- A probability measure `π` is stationary for a Markov kernel `κ` if evolving `π` by one step
of `κ` leaves it unchanged: `κ ∘ₘ π = π`. This is the discrete-time analogue of thermal
equilibrium. -/
def IsStationary {Ω : Type*} {mΩ : MeasurableSpace Ω} (κ : Kernel Ω Ω) (π : Measure Ω) : Prop :=
  κ ∘ₘ π = π

end SecondLaw
