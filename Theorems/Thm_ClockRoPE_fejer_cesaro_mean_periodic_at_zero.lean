import Mathlib

namespace ClockRoPE

/-- **Fejér's theorem, specialized at the origin.** For `f : ℝ → ℝ` continuous and `T`-periodic
with (real) Fourier cosine coefficients `α k = (1/T) ∫_0^T f(x) cos(2πkx/T) dx`, the Cesàro
(Fejér) means of the symmetric partial sums `S_n = ∑_{k=-n}^{n} α k` of its Fourier series,
evaluated at `x = 0`, converge to `f 0`. This is Fejér's 1904 theorem — uniform convergence of
the Cesàro means of the Fourier series of a continuous periodic function to the function itself
— specialized to the single point `x = 0`, where every harmonic `cos(2πk·0/T) = 1`, so that the
`n`-th partial sum there is exactly `S_n = ∑_{k=-n}^{n} α k`. -/
theorem fejer_cesaro_mean_periodic_at_zero
    (f : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (hf_cont : Continuous f)
    (hf_periodic : ∀ x : ℝ, f (x + T) = f x)
    (α : ℤ → ℝ)
    (hα : ∀ k : ℤ, α k =
      (1 / T) * ∫ x in (0 : ℝ)..T, f x * Real.cos (2 * Real.pi * (k : ℝ) * x / T)) :
    Filter.Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) *
        ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.Icc (-(n : ℤ)) n, α k)
      Filter.atTop (nhds (f 0)) := by
  sorry

end ClockRoPE
