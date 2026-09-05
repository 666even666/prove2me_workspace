import Mathlib
import Definitions.Def_PosDefKernel
import Definitions.Def_RandomFourierRotation

namespace ClockRoPE

open MeasureTheory

/-- **Proposition 3.1 (Random Fourier Rotation Estimator).**
Let `f : ℝ → ℝ` be a continuous, Lebesgue-integrable, positive-definite kernel with `f 0 = 1`,
and let `τ` be its Fourier transform. For query `q_m ∈ ℝ^{2n}` and key `k_n ∈ ℝ^{2n}` at
positions `p_m, p_n ∈ ℝ`, sample `n` i.i.d. frequencies `ξ_0, …, ξ_{n-1} ∼ τ` and form the
Random Fourier Rotation estimator `ĝ(q_m, k_n, p_m, p_n)` by rotating each feature pair of
`q_m`/`k_n` by the angle `2πξ_j p_m`/`2πξ_j p_n` and summing the pairwise dot products. Then
`ĝ` is an unbiased estimator of `q_m^⊤ k_n · f(p_m - p_n)`. -/
theorem rfr_estimator_unbiased
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPosDefKernel f) (hf0 : f 0 = 1)
    (n : ℕ) (q k : Fin (2 * n) → ℝ) (pm pn : ℝ) :
    ∫ ξ : Fin n → ℝ, rfrEstimator n q k pm pn ξ
        ∂(Measure.pi fun _ : Fin n =>
            (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (fourierTransform f x))
      = dotProduct q k * f (pm - pn) := by
  sorry

end ClockRoPE
