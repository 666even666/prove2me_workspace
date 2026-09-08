import Definitions.Def_DDPM_core

/-!
# DDPM: forward process, reverse process, and the terms of the variational bound

Jonathan Ho, Ajay Jain, Pieter Abbeel, *Denoising Diffusion Probabilistic Models*,
NeurIPS 2020, https://arxiv.org/abs/2006.11239, Sections 2-3, Eqs. (1)-(11).

A trajectory `x_{0:T}` is a function `x : Fin (T+1) → Space d`.  A step index `i : Fin T`
stands for the paper's time step `t = i + 1`, so `x i.castSucc = x_{t-1}` and `x i.succ = x_t`.
Model parameters (`μ_θ(·,t)`, `σ_t²`, `ε_θ(·,t)`) are families indexed by `t : ℕ`; only their
values at `t = 1, …, T` are used.
-/

namespace DDPM

open MeasureTheory Real

variable {d : ℕ}

/-- The forward (diffusion) process density
`q(x_{1:T} | x_0) = ∏_{t=1}^{T} N(x_t; √(1-β_t) x_{t-1}, β_t I)` (Eq. 2). -/
noncomputable def qCond (s : Schedule) (T : ℕ) (x : Fin (T + 1) → Space d) : ℝ :=
  ∏ i : Fin T,
    gaussPDF (Real.sqrt (1 - s.beta ((i : ℕ) + 1)) • x i.castSucc) (s.beta ((i : ℕ) + 1)) (x i.succ)

/-- The reverse process density
`p_θ(x_{0:T}) = N(x_T; 0, I) ∏_{t=1}^{T} N(x_{t-1}; μ_θ(x_t,t), σ_t² I)` (Eq. 1). -/
noncomputable def pJoint (T : ℕ) (mu : ℕ → Space d → Space d) (v : ℕ → ℝ)
    (x : Fin (T + 1) → Space d) : ℝ :=
  gaussPDF (0 : Space d) 1 (x (Fin.last T)) *
    ∏ i : Fin T, gaussPDF (mu ((i : ℕ) + 1) (x i.succ)) (v ((i : ℕ) + 1)) (x i.castSucc)

/-- The closed-form forward marginal of Eq. (4): `N(x; √ᾱ_t x_0, (1-ᾱ_t) I)`. -/
noncomputable def qMarginal (s : Schedule) (t : ℕ) (x0 x : Space d) : ℝ :=
  gaussPDF (Real.sqrt (alphaBar s t) • x0) (1 - alphaBar s t) x

/-- The law of `x_t` given `x_0` under the forward process, obtained by iterated one-step
marginalization of Eq. (2).  Only `t ≥ 1` is meaningful. -/
noncomputable def qFwd (s : Schedule) (x0 : Space d) : ℕ → Space d → ℝ
  | 0 => fun _ => 0
  | 1 => fun x => gaussPDF (Real.sqrt (1 - s.beta 1) • x0) (s.beta 1) x
  | (n + 2) => fun x =>
      ∫ y, qFwd s x0 (n + 1) y *
        gaussPDF (Real.sqrt (1 - s.beta (n + 2)) • y) (s.beta (n + 2)) x

/-- The forward-process posterior mean
`μ̃_t(x_t,x_0) = (√ᾱ_{t-1} β_t)/(1-ᾱ_t) · x_0 + (√α_t (1-ᾱ_{t-1}))/(1-ᾱ_t) · x_t` (Eq. 7). -/
noncomputable def posteriorMean (s : Schedule) (t : ℕ) (xt x0 : Space d) : Space d :=
  (Real.sqrt (alphaBar s (t - 1)) * s.beta t / (1 - alphaBar s t)) • x0 +
    (Real.sqrt (alpha s t) * (1 - alphaBar s (t - 1)) / (1 - alphaBar s t)) • xt

/-- The forward-process posterior variance `β̃_t = (1-ᾱ_{t-1})/(1-ᾱ_t) · β_t` (Eq. 7). -/
noncomputable def posteriorVar (s : Schedule) (t : ℕ) : ℝ :=
  (1 - alphaBar s (t - 1)) / (1 - alphaBar s t) * s.beta t

/-- The reparameterized forward sample `x_t(x_0, ε) = √ᾱ_t x_0 + √(1-ᾱ_t) ε` (Section 3.2). -/
noncomputable def noised (s : Schedule) (t : ℕ) (x0 e : Space d) : Space d :=
  Real.sqrt (alphaBar s t) • x0 + Real.sqrt (1 - alphaBar s t) • e

/-- The ε-parameterization of the reverse-process mean,
`μ_θ(x_t,t) = (1/√α_t) (x_t - β_t/√(1-ᾱ_t) · ε_θ(x_t,t))` (Eq. 11). -/
noncomputable def muEps (s : Schedule) (eps : ℕ → Space d → Space d)
    (t : ℕ) (xt : Space d) : Space d :=
  (1 / Real.sqrt (alpha s t)) •
    (xt - (s.beta t / Real.sqrt (1 - alphaBar s t)) • eps t xt)

/-- The model likelihood `p_θ(x_0) = ∫ p_θ(x_{0:T}) dx_{1:T}` (Section 2). -/
noncomputable def pMarginal (T : ℕ) (mu : ℕ → Space d → Space d) (v : ℕ → ℝ)
    (x0 : Space d) : ℝ :=
  ∫ y : Fin T → Space d, pJoint T mu v (Fin.cons x0 y)

/-- The variational bound of Eq. (3) conditioned on the data point `x_0`:
`L(x_0) = E_{q(x_{1:T}|x_0)}[-log (p_θ(x_{0:T}) / q(x_{1:T}|x_0))]`. -/
noncomputable def vbCond (s : Schedule) (T : ℕ) (mu : ℕ → Space d → Space d) (v : ℕ → ℝ)
    (x0 : Space d) : ℝ :=
  ∫ y : Fin T → Space d,
    (-Real.log (pJoint T mu v (Fin.cons x0 y) / qCond s T (Fin.cons x0 y))) *
      qCond s T (Fin.cons x0 y)

/-- The variational bound `L = E_q[-log (p_θ(x_{0:T}) / q(x_{1:T}|x_0))]` (Eq. 3),
averaged over a data density `q0`. -/
noncomputable def vb (s : Schedule) (T : ℕ) (mu : ℕ → Space d → Space d) (v : ℕ → ℝ)
    (q0 : Space d → ℝ) : ℝ :=
  ∫ x0, q0 x0 * vbCond s T mu v x0

/-- `L_T = D_KL(q(x_T|x_0) ‖ p(x_T))` (Eq. 5). -/
noncomputable def termT (s : Schedule) (T : ℕ) (x0 : Space d) : ℝ :=
  klPDF (qMarginal s T x0) (gaussPDF (0 : Space d) 1)

/-- `L_{t-1} = E_{q(x_t|x_0)} D_KL(q(x_{t-1}|x_t,x_0) ‖ p_θ(x_{t-1}|x_t))` (Eq. 5). -/
noncomputable def termMid (s : Schedule) (mu : ℕ → Space d → Space d) (v : ℕ → ℝ)
    (t : ℕ) (x0 : Space d) : ℝ :=
  ∫ xt, qMarginal s t x0 xt *
    klPDF (gaussPDF (posteriorMean s t xt x0) (posteriorVar s t)) (gaussPDF (mu t xt) (v t))

/-- `L_0 = E_{q(x_1|x_0)}[-log p_θ(x_0|x_1)]` (Eq. 5). -/
noncomputable def term0 (s : Schedule) (mu : ℕ → Space d → Space d) (v : ℕ → ℝ)
    (x0 : Space d) : ℝ :=
  ∫ x1, qMarginal s 1 x0 x1 * (-Real.log (gaussPDF (mu 1 x1) (v 1) x0))

end DDPM
