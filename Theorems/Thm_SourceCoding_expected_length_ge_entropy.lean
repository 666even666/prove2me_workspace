import Mathlib
import Definitions.Def_SourceCoding_entropy

namespace SourceCoding

/-- **Shannon's source coding theorem, lower bound.** For any probability distribution
`p : ι → ℝ` (`p i > 0`, `∑ p i = 1`) and any uniquely decodable `D`-ary code
`c : ι → List α` (`D = Fintype.card α ≥ 2`) assigning a distinct codeword to each source
symbol, the expected codeword length is at least the source's entropy: `H_D(p) ≤ ∑ p i * |c i|`. -/
theorem expected_length_ge_entropy
    {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp_pos : ∀ i, 0 < p i)
    (hp_sum : ∑ i, p i = 1)
    {α : Type} [Fintype α] [Nonempty α] (hD : 2 ≤ Fintype.card α)
    (c : ι → List α) (hinj : Function.Injective c)
    (hc : InformationTheory.UniquelyDecodable (Set.range c)) :
    entropy p (Fintype.card α) ≤ ∑ i, p i * (c i).length := by
  sorry

end SourceCoding
