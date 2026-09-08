import Mathlib

namespace Grover

/-- The Grover oracle for a marked index `w0`: the reflection `I - 2|w0⟩⟨w0|`, which flips the
sign of the amplitude on the marked basis state `|w0⟩` and leaves every other basis state fixed. -/
noncomputable def oracle {N : ℕ} (w0 : Fin N) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  ContinuousLinearMap.id ℂ _ -
    (2 : ℂ) • InnerProductSpace.rankOne ℂ
      (EuclideanSpace.single w0 (1 : ℂ)) (EuclideanSpace.single w0 (1 : ℂ))

end Grover
