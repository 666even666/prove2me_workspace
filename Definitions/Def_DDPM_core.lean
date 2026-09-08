import Mathlib

/-!
# DDPM: variance schedule, isotropic Gaussian density, KL divergence

Notation for the formalization of

  Jonathan Ho, Ajay Jain, Pieter Abbeel,
  *Denoising Diffusion Probabilistic Models*, NeurIPS 2020,
  https://arxiv.org/abs/2006.11239

Section 2 of the paper.  Time is indexed by `t : ℕ` exactly as in the paper, with the
forward process running `t = 1, …, T`.
-/

namespace DDPM

open MeasureTheory Real

/-- The data space `ℝ^d` on which the diffusion model lives. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A forward-process variance schedule `β_1, β_2, …` with `0 < β_t < 1`
(paper, Eq. 2: the `β_t` are the variances of the forward Markov chain). -/
structure Schedule where
  beta : ℕ → ℝ
  beta_pos : ∀ t, 0 < beta t
  beta_lt_one : ∀ t, beta t < 1

/-- `α_t := 1 - β_t` (paper, Section 2). -/
def alpha (s : Schedule) (t : ℕ) : ℝ := 1 - s.beta t

/-- `ᾱ_n := ∏_{t=1}^{n} α_t` (paper, Section 2).  In particular `ᾱ_0 = 1`. -/
def alphaBar (s : Schedule) (n : ℕ) : ℝ := ∏ t ∈ Finset.Icc 1 n, alpha s t

/-- The density at `x` of the isotropic Gaussian `N(m, v · I)` on `ℝ^d`:
`(2πv)^{-d/2} exp(-‖x - m‖² / (2v))`.  This is the paper's `N(x; m, v I)`. -/
noncomputable def gaussPDF {d : ℕ} (m : Space d) (v : ℝ) (x : Space d) : ℝ :=
  (2 * π * v) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - m‖ ^ 2 / (2 * v))

/-- The Kullback-Leibler divergence `D_KL(f ‖ g) = ∫ f log (f / g)` between two
probability densities on `ℝ^d`. -/
noncomputable def klPDF {d : ℕ} (f g : Space d → ℝ) : ℝ := ∫ x, f x * Real.log (f x / g x)

end DDPM
