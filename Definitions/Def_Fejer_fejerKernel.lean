import Mathlib

namespace Fejer

/-- The `N`-th Fejér kernel, `F_N(θ) = ∑_{n=-N}^{N} (1 - |n|/(N+1)) cos(nθ)` — the real-valued
function whose convolution against `f` computes the `N`-th Cesàro mean of `f`'s Fourier series. -/
noncomputable def fejerKernel (N : ℕ) (θ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 - (|n| : ℝ) / (N + 1)) * Real.cos (n * θ)

end Fejer
