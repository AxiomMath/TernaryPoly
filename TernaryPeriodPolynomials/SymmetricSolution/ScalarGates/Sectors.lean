module

public import TernaryPeriodPolynomials.SymmetricSolution.ScalarGates.Defs

@[expose] public section


noncomputable section
namespace TernaryPoly.ScalarGates

/-- The two explicit mathematical assertions imply support in every positive symmetric degree. -/
theorem symmetric_pairwise (hscalar : ScalarZero) (hordinary : SectorReferencePairwise)
    {n : ℕ} {f : TernaryPolynomial} (hn : 0<n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f=f) : Pairwise f := by
  have hJ := todd_zero_of_scalar_gate hscalar hn hf hrel hs
  obtain ⟨Φ,hΦ,hreference⟩ :=
    symmetric_all_degree_Todd_zero_ordinary_cycle_extension hn hf hrel hs hJ
  change referenceValue n Φ=f at hreference
  have hp := hordinary.1 n hn Φ hΦ
    (by simpa only [hreference] using hrel)
    (by simpa only [hreference] using hs)
    (by simpa only [hreference] using hJ)
  simpa only [hreference] using hp

/-- Only the actual untwisted even-degree support assertion is needed in this sector. -/
theorem even_alternating_pairwise (hordinary : SectorReferencePairwise)
    {n : ℕ} {f : TernaryPolynomial} (hn : 0<n) (he : Even n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f= -f) : Pairwise f := by
  obtain ⟨Φ,hΦ,hreference⟩ := alternating_ordinary_extension he hf hrel hs
  change referenceValue n Φ=f at hreference
  have hp := hordinary.2 n hn he Φ hΦ
    (by simpa only [hreference] using hrel)
    (by simpa only [hreference] using hs)
  simpa only [hreference] using hp

/-- Odd alternating support is already proved and requires neither unresolved assertion. -/
theorem odd_alternating_pairwise {n : ℕ} {f : TernaryPolynomial}
    (ho : Odd n) (hf : f.IsHomogeneous n) (hrel : PeriodRelations f) (hs : S f= -f) :
    Pairwise f := by
  rw [odd_alternating_eq_zero hf ho hrel.1 hs hrel.2]
  exact pairwise_zero

/-- The actual support assertion and odd vanishing handle all positive alternating degrees. -/
theorem alternating_pairwise (hordinary : SectorReferencePairwise)
    {n : ℕ} {f : TernaryPolynomial} (hn : 0<n) (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f= -f) : Pairwise f := by
  rcases Nat.even_or_odd n with he | ho
  · exact even_alternating_pairwise hordinary hn he hf hrel hs
  · exact odd_alternating_pairwise ho hf hrel hs

end TernaryPoly.ScalarGates
