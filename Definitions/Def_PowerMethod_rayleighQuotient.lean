import Mathlib

namespace PowerMethod

/-- The Rayleigh quotient of a linear map `T` at a nonzero vector `x`,
`R_T(x) = ⟪x, T x⟫ / ‖x‖²`, whose value at an eigenvector of `T` equals the corresponding
eigenvalue. -/
noncomputable def rayleighQuotient {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (T : E →ₗ[𝕜] E) (x : E) : ℝ :=
  RCLike.re (inner (𝕜 := 𝕜) x (T x)) / ‖x‖ ^ 2

end PowerMethod
