import Mathlib
import Definitions.Def_Grover_oracle
import Definitions.Def_Grover_diffusion

namespace Grover

/-- One step of Grover's algorithm: the diffusion operator applied after the oracle,
`G = (2|s⟩⟨s| - I)(I - 2|w0⟩⟨w0|)`. -/
noncomputable def groverIterate {N : ℕ} (w0 : Fin N) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  diffusion N ∘L oracle w0

end Grover
