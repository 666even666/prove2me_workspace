import Mathlib

namespace SourceCoding

/-- **Kraft–McMillan inequality** (McMillan, 1956). If `S` is a finite uniquely decodable
`D`-ary code (`D = Fintype.card α`), then `∑_{w ∈ S} D^{-|w|} ≤ 1`. -/
theorem kraft_mcmillan_inequality
    {α : Type} [Fintype α] [Nonempty α] (S : Finset (List α))
    (h : InformationTheory.UniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / (Fintype.card α : ℝ)) ^ w.length ≤ 1 := by
  sorry

end SourceCoding
