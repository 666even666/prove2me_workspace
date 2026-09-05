import Mathlib
import Definitions.Def_PosDefKernel
import Definitions.Def_RandomFourierRotation

namespace ClockRoPE

open MeasureTheory

/-- **Proposition 3.2 (Convergence of Random Fourier Rotation Estimator).**
Under the same setting as `rfr_estimator_unbiased` (a continuous, integrable, positive-definite
kernel `f` with `f 0 = 1`, its Fourier transform `τ`, `n` i.i.d. frequencies `ξ_0, …, ξ_{n-1} ∼
τ`, and query/key vectors `q_m, k_n ∈ ℝ^{2n}` at positions `p_m, p_n`), the averaged estimator
`(1/n) · ĝ(q_m, k_n, p_m, p_n)` concentrates around `(1/n) · q_m^⊤ k_n · f(p_m - p_n)` at a rate
governed by a McDiarmid-type exponential tail bound. -/
theorem rfr_estimator_concentration
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f (volume : Measure ℝ))
    (hf_pd : IsPosDefKernel f) (hf0 : f 0 = 1)
    (n : ℕ) (q k : Fin (2 * n) → ℝ) (pm pn : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin n =>
        (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (fourierTransform f x))
        {ξ : Fin n → ℝ |
          ε ≤ |(1 / (n : ℝ)) * rfrEstimator n q k pm pn ξ
                - (1 / (n : ℝ)) * (dotProduct q k * f (pm - pn))|}
      ≤ ENNReal.ofReal
          (2 * Real.exp (-(ε ^ 2 * (2 * (n : ℝ)) ^ 2 /
            (8 * ∑ j : Fin n,
              (pairNorm (featurePair n q j) * pairNorm (featurePair n k j)) ^ 2)))) := by
  sorry

end ClockRoPE
