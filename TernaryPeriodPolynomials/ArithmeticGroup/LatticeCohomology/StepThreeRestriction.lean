module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.StepThreeIndex
public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.RestrictionEmbedding

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open CategoryTheory LatticeTopCohomology

/-- Restriction of any rational coefficient representation along the actual step-three
radical parameter map is injective in every cohomological degree. -/
theorem scaleLattice_three_restriction_injective (A : Rep ℚ Lattice) (n : ℕ) :
    Function.Injective (groupCohomology.map (scaleLattice 3)
      (𝟙 (Rep.res (scaleLattice 3) A)) n) :=
  RationalCohomologyRestriction.restriction_embedding_injective (scaleLattice 3)
    scaleLattice_three_injective A n

theorem scaleLattice_three_restriction_zero_iff (A : Rep ℚ Lattice) (n : ℕ)
    (v : groupCohomology A n) :
    groupCohomology.map (scaleLattice 3) (𝟙 (Rep.res (scaleLattice 3) A)) n v=0 ↔ v=0 := by
  constructor
  · intro hv
    apply scaleLattice_three_restriction_injective A n
    simpa only [map_zero] using hv
  · rintro rfl
    exact map_zero _

end TernaryPoly.OrdinaryFaceRadical
