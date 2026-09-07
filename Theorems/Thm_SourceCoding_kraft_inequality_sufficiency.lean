import Mathlib

namespace SourceCoding

/-- **Kraft's inequality, sufficiency direction** (Kraft, 1949). If `D = Fintype.card α ≥ 2`
and integer lengths `ℓ : ι → ℕ` satisfy the Kraft sum bound `∑ i, D^{-ℓ i} ≤ 1`, there is an
injective assignment `c : ι → List α` of distinct codewords with `(c i).length = ℓ i` for every
`i`, whose codeword set is uniquely decodable. -/
theorem kraft_inequality_sufficiency
    {α : Type} [Fintype α] [Nonempty α] {ι : Type} [Fintype ι]
    (ℓ : ι → ℕ) (hK : ∑ i, (1 / (Fintype.card α : ℝ)) ^ ℓ i ≤ 1) :
    ∃ c : ι → List α, Function.Injective c ∧ (∀ i, (c i).length = ℓ i) ∧
      InformationTheory.UniquelyDecodable (Set.range c) := by
  sorry

end SourceCoding
