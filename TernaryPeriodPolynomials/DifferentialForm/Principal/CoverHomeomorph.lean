module

public import TernaryPeriodPolynomials.DifferentialForm.Principal.DeckEquiv
public import TernaryPeriodPolynomials.SymmetricSpace.SingularOrbits
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityCoverHomeomorph

@[expose] public section


/-! The actual arithmetic quotient homeomorphism is a genuine equivariant covering square. -/
noncomputable section
namespace TernaryPoly.PolynomialFormPrincipalCover
open CategoryTheory PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceBordifiedCohomology SymmetricSpaceBordifiedPrincipalSix
  SingularLocalCompactDuality

/-- The principal interior map is also a quotient cover for the isomorphic nested deck group. -/
theorem interiorDeckQuotientCovering : IsQuotientCoveringMap interiorCover DeckGroup :=
  quotientProjection_quotientCovering.homeomorph_comp arithmeticInteriorHomeomorph

/-- Identity on positive forms and the actual orbit-quotient homeomorphism downstairs. -/
def arithmeticCoverHomeomorph :
    CoverHomeomorph (G := DeckGroup) singularCoveringProjection interiorCover where
  total := Homeomorph.refl Space
  base := arithmeticInteriorHomeomorph
  square := rfl
  equivariant _ _ := rfl

end TernaryPoly.PolynomialFormPrincipalCover
