import Mathlib
import Definitions.Def_uniformSuperposition

namespace Grover

/-- The Grover diffusion operator: the reflection `2|s⟩⟨s| - I` about the uniform superposition
`|s⟩`, also called "inversion about the mean". -/
noncomputable def diffusion (N : ℕ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (2 : ℂ) • InnerProductSpace.rankOne ℂ (uniformSuperposition N) (uniformSuperposition N) -
    ContinuousLinearMap.id ℂ _

end Grover
