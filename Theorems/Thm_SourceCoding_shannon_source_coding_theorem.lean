import Mathlib
import Definitions.Def_SourceCoding_entropy

namespace SourceCoding

/-- **Shannon's source coding theorem** (Shannon, 1948). For a source with probability
distribution `p : ι → ℝ` (`p i > 0`, `∑ p i = 1`) and a `D`-ary code alphabet (`D =
Fintype.card α ≥ 2`): every uniquely decodable code assigning distinct codewords to the source
symbols has expected length at least the source's entropy `H_D(p)`, and there exists a uniquely
decodable code whose expected length is within one symbol of this bound, `< H_D(p) + 1`. -/
theorem shannon_source_coding_theorem
    {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp_pos : ∀ i, 0 < p i)
    (hp_sum : ∑ i, p i = 1)
    {α : Type} [Fintype α] [Nonempty α] (hD : 2 ≤ Fintype.card α) :
    (∀ c : ι → List α, Function.Injective c →
        InformationTheory.UniquelyDecodable (Set.range c) →
        entropy p (Fintype.card α) ≤ ∑ i, p i * (c i).length) ∧
    (∃ c : ι → List α, Function.Injective c ∧
        InformationTheory.UniquelyDecodable (Set.range c) ∧
        ∑ i, p i * (c i).length < entropy p (Fintype.card α) + 1) := by
  sorry

end SourceCoding
