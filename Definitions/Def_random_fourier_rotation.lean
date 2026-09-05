import Mathlib

namespace ClockRoPE

/-- The 2D (Givens) rotation matrix by angle `θ`. -/
noncomputable def rotation2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The `j`-th consecutive 2D feature pair `(v (2j), v (2j+1))` of a `2n`-dimensional vector
`v`, grouping its features into `n` disjoint pairs as in RoPE-style rotations. -/
def featurePair (n : ℕ) (v : Fin (2 * n) → ℝ) (j : Fin n) : Fin 2 → ℝ :=
  ![v ⟨2 * j.1, by have := j.2; omega⟩, v ⟨2 * j.1 + 1, by have := j.2; omega⟩]

/-- The Euclidean norm of a 2D feature pair. -/
noncomputable def pairNorm (v : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (v 0 ^ 2 + v 1 ^ 2)

/-- The Random Fourier Rotation estimator `ĝ(q_m, k_n, p_m, p_n)`: for each of the `n` feature
pairs, rotate the query and key pair by the frequency-scaled angles `2πξ_j p_m` and `2πξ_j p_n`
respectively, then sum the pairwise dot products of the rotated pairs. -/
noncomputable def rfrEstimator (n : ℕ) (q k : Fin (2 * n) → ℝ) (pm pn : ℝ) (ξ : Fin n → ℝ) :
    ℝ :=
  ∑ j : Fin n,
    dotProduct
      (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pm)) (featurePair n q j))
      (Matrix.mulVec (rotation2 (2 * Real.pi * ξ j * pn)) (featurePair n k j))

end ClockRoPE
