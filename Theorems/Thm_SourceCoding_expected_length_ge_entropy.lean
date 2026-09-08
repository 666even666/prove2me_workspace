import Mathlib
import Definitions.Def_SourceCoding_entropy
import Theorems.Thm_SourceCoding_kraft_mcmillan_inequality

namespace SourceCoding

/-- **Shannon's source coding theorem, lower bound.** For any probability distribution
`p : ι → ℝ` (`p i > 0`, `∑ p i = 1`) and any uniquely decodable `D`-ary code
`c : ι → List α` (`D = Fintype.card α ≥ 2`) assigning a distinct codeword to each source
symbol, the expected codeword length is at least the source's entropy: `H_D(p) ≤ ∑ p i * |c i|`.

Proved via the Kraft–McMillan inequality (Milestone 1) applied to the code's image, combined
with the weighted AM–GM inequality (`Real.geom_mean_le_arith_mean_weighted`) applied to the
weights `p i` and the ratios `z i = D^{-|c i|} / p i` — the standard Gibbs'-inequality argument
for the source coding lower bound. -/
theorem expected_length_ge_entropy
    {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp_pos : ∀ i, 0 < p i)
    (hp_sum : ∑ i, p i = 1)
    {α : Type} [Fintype α] [Nonempty α] (hD : 2 ≤ Fintype.card α)
    (c : ι → List α) (hinj : Function.Injective c)
    (hc : InformationTheory.UniquelyDecodable (Set.range c)) :
    entropy p (Fintype.card α) ≤ ∑ i, p i * (c i).length := by
  classical
  set D : ℝ := (Fintype.card α : ℝ) with hDdef
  have hDpos : (0 : ℝ) < D := by
    rw [hDdef]
    have : (0 : ℕ) < Fintype.card α := by omega
    exact_mod_cast this
  have hD1 : (1 : ℝ) < D := by
    rw [hDdef]
    have : (1 : ℕ) < Fintype.card α := by omega
    exact_mod_cast this
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  -- Kraft sum for this code, from Milestone 1 applied to the (finite, injective) image of `c`.
  have hKraft : ∑ i, (1 / D) ^ (c i).length ≤ 1 := by
    have hSeq : ((Finset.image c Finset.univ : Finset (List α)) : Set (List α))
        = Set.range c := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hUD : InformationTheory.UniquelyDecodable
        ((Finset.image c Finset.univ : Finset (List α)) : Set (List α)) := by
      rw [hSeq]; exact hc
    have hkm := kraft_mcmillan_inequality (Finset.image c Finset.univ) hUD
    have hSum : ∑ w ∈ Finset.image c Finset.univ, (1 / (Fintype.card α : ℝ)) ^ w.length
        = ∑ i, (1 / (Fintype.card α : ℝ)) ^ (c i).length := by
      apply Finset.sum_image
      intro x _ y _ hxy
      exact hinj hxy
    rw [hSum] at hkm
    exact hkm
  -- Weighted AM–GM applied to the weights `p` and the ratios `z i = D^{-ℓ i} / p i`.
  set z : ι → ℝ := fun i => (1 / D) ^ (c i).length / p i with hzdef
  have hz_pos : ∀ i, 0 < z i := by
    intro i
    apply div_pos
    · positivity
    · exact hp_pos i
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ p z
    (fun i _ => (hp_pos i).le) hp_sum (fun i _ => (hz_pos i).le)
  have hrhs : ∑ i, p i * z i ≤ 1 := by
    have heq : ∑ i, p i * z i = ∑ i, (1 / D) ^ (c i).length := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hzdef]
      field_simp [(hp_pos i).ne']
    rw [heq]
    exact hKraft
  have hlhs_pos : 0 < ∏ i, z i ^ p i := by
    apply Finset.prod_pos
    intro i _
    exact Real.rpow_pos_of_pos (hz_pos i) _
  have hle : ∏ i, z i ^ p i ≤ 1 := le_trans hamgm hrhs
  have hlog_le : Real.log (∏ i, z i ^ p i) ≤ 0 := by
    calc Real.log (∏ i, z i ^ p i) ≤ Real.log 1 :=
          (Real.log_le_log_iff hlhs_pos one_pos).2 hle
      _ = 0 := Real.log_one
  have hlog_prod : Real.log (∏ i, z i ^ p i) = ∑ i, p i * Real.log (z i) := by
    rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hz_pos i) (p i)).ne')]
    apply Finset.sum_congr rfl
    intro i _
    exact Real.log_rpow (hz_pos i) (p i)
  rw [hlog_prod] at hlog_le
  have hlogz : ∀ i, Real.log (z i) = -(((c i).length : ℝ)) * Real.log D - Real.log (p i) := by
    intro i
    rw [hzdef]
    show Real.log ((1 / D) ^ (c i).length / p i) = _
    rw [Real.log_div (by positivity) (hp_pos i).ne', Real.log_pow, Real.log_div one_ne_zero
      hDpos.ne', Real.log_one]
    ring
  simp_rw [hlogz] at hlog_le
  have step1 : ∑ i, p i * (-(((c i).length : ℝ)) * Real.log D - Real.log (p i))
      = ∑ i, (-(p i * (c i).length) * Real.log D - p i * Real.log (p i)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have step2 : ∑ i, (-(p i * (c i).length) * Real.log D - p i * Real.log (p i))
      = -(∑ i, p i * (c i).length) * Real.log D - ∑ i, p i * Real.log (p i) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_neg_distrib]
  rw [step1, step2] at hlog_le
  have hentropy : entropy p (Fintype.card α) = -(∑ i, p i * Real.log (p i)) / Real.log D := by
    show -∑ i, p i * Real.logb (Fintype.card α) (p i) = _
    rw [← hDdef]
    have hpt : ∀ i, p i * Real.logb D (p i) = (p i * Real.log (p i)) / Real.log D := by
      intro i
      rw [← Real.log_div_log, mul_div_assoc]
    simp_rw [hpt, ← Finset.sum_div]
    ring
  rw [hentropy]
  rw [div_le_iff₀ hlogD]
  linarith

end SourceCoding
