import Mathlib
import Definitions.Def_SourceCoding_entropy

namespace SourceCoding

/-- **Shannon's source coding theorem** (Shannon, 1948) — corrected, superseding
`SourceCoding.shannon_source_coding_theorem`, which omitted the hypothesis that the source has
at least two symbols: `Nonempty ι` alone permits `Fintype.card ι = 1`, forcing `p ≡ 1` and
entropy `0`, so the achievability conjunct would demand a codeword of length `0` — impossible,
since a uniquely decodable code can never contain the empty codeword
(`InformationTheory.UniquelyDecodable.epsilon_not_mem`). With `2 ≤ Fintype.card ι`, full
support forces every `p i < 1` strictly, so the Shannon–Fano lengths `⌈-log_D (p i)⌉` are all
at least `1` and the classical argument goes through. For a source with probability
distribution `p : ι → ℝ` (`p i > 0`, `∑ p i = 1`, at least two symbols) and a `D`-ary code
alphabet (`D = Fintype.card α ≥ 2`): every uniquely decodable code assigning distinct
codewords to the source symbols has expected length at least the source's entropy `H_D(p)`,
and there exists a uniquely decodable code whose expected length is within one symbol of this
bound, `< H_D(p) + 1`. -/
theorem shannon_source_coding_theorem_v2
    {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp_pos : ∀ i, 0 < p i)
    (hp_sum : ∑ i, p i = 1) (hι : 2 ≤ Fintype.card ι)
    {α : Type} [Fintype α] [Nonempty α] (hD : 2 ≤ Fintype.card α) :
    (∀ c : ι → List α, Function.Injective c →
        InformationTheory.UniquelyDecodable (Set.range c) →
        entropy p (Fintype.card α) ≤ ∑ i, p i * (c i).length) ∧
    (∃ c : ι → List α, Function.Injective c ∧
        InformationTheory.UniquelyDecodable (Set.range c) ∧
        ∑ i, p i * (c i).length < entropy p (Fintype.card α) + 1) := by
  sorry

end SourceCoding
