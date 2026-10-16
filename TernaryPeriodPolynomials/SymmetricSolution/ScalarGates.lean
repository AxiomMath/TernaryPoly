module

public import TernaryPeriodPolynomials.SymmetricSolution.ScalarGates.Sectors

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.ScalarGates

/-- The complete scalar assertion and weaker actual sector-support assertion imply pairwise
support for arbitrary solutions, with no degree bound or homogeneity premise. -/
theorem pairwise_of_two_sector_gates (hscalar : ScalarZero) (hordinary : SectorReferencePairwise)
    {f : TernaryPolynomial} (hrel : PeriodRelations f) : Pairwise f := by
  apply pairwise_of_positive_homogeneous_sectors (f := f) _ _ hrel
  · intro n g hn hg hr hs
    exact symmetric_pairwise hscalar hordinary hn hg hr hs
  · intro n g hn hg hr hs
    exact alternating_pairwise hordinary hn hg hr hs

/-- The exact conclusion, conditional only on complete scalar vanishing and
actual sector-compatible ordinary reference support. -/
theorem benchmark_of_two_sector_gates (hscalar : ScalarZero) (hordinary : SectorReferencePairwise)
    (f : MvPolynomial (Fin 3) ℚ)
    (hcyclic : bind₁ ![X 1,X 2,X 0] f=f)
    (hnorm : f+bind₁ ![-X 1,X 0-X 1,X 2] f+
      bind₁ ![X 1-X 0,-X 0,X 2] f=0) :
    ∃ p q r : MvPolynomial (Fin 2) ℚ,
      f=rename (![0,1] : Fin 2 → Fin 3) p+
        rename (![1,2] : Fin 2 → Fin 3) q+
        rename (![0,2] : Fin 2 → Fin 3) r :=
  (pairwise_of_two_sector_gates hscalar hordinary ⟨hcyclic,hnorm⟩).exists_rename

/-- The two mathematical assertions suffice for the exact conclusion.
This theorem takes both assertions as hypotheses. -/
theorem benchmark_of_two_actual_gates (hscalar : ScalarZero) (hordinary : OrdinaryReferencePairwise)
    (f : MvPolynomial (Fin 3) ℚ)
    (hcyclic : bind₁ ![X 1,X 2,X 0] f=f)
    (hnorm : f+bind₁ ![-X 1,X 0-X 1,X 2] f+
      bind₁ ![X 1-X 0,-X 0,X 2] f=0) :
    ∃ p q r : MvPolynomial (Fin 2) ℚ,
      f=rename (![0,1] : Fin 2 → Fin 3) p+
        rename (![1,2] : Fin 2 → Fin 3) q+
        rename (![0,2] : Fin 2 → Fin 3) r :=
  benchmark_of_two_sector_gates hscalar (sectorReferencePairwise_of_ordinary hordinary)
    f hcyclic hnorm

end TernaryPoly.ScalarGates
