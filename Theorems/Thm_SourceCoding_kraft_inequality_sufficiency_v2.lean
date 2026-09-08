import Mathlib

namespace SourceCoding

/-- **Kraft's inequality, sufficiency direction** (Kraft, 1949) — corrected, superseding
`SourceCoding.kraft_inequality_sufficiency`, which omitted the hypothesis that lengths are
positive: since a uniquely decodable code can never contain the empty codeword
(`InformationTheory.UniquelyDecodable.epsilon_not_mem`), the original statement is false
whenever some `ℓ i = 0` (e.g. a singleton `ι` with `ℓ = 0` satisfies the Kraft sum bound
vacuously but admits no valid code). If `D = Fintype.card α ≥ 2` and integer lengths
`ℓ : ι → ℕ`, all strictly positive, satisfy the Kraft sum bound `∑ i, D^{-ℓ i} ≤ 1`, there is
an injective assignment `c : ι → List α` of distinct codewords with `(c i).length = ℓ i` for
every `i`, whose codeword set is uniquely decodable. -/
theorem kraft_inequality_sufficiency_v2
    {α : Type} [Fintype α] [Nonempty α] {ι : Type} [Fintype ι]
    (ℓ : ι → ℕ) (hℓ_pos : ∀ i, 0 < ℓ i) (hK : ∑ i, (1 / (Fintype.card α : ℝ)) ^ ℓ i ≤ 1) :
    ∃ c : ι → List α, Function.Injective c ∧ (∀ i, (c i).length = ℓ i) ∧
      InformationTheory.UniquelyDecodable (Set.range c) := by
  sorry

end SourceCoding
