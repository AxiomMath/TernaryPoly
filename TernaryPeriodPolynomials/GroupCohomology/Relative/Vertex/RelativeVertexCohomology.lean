module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyExtension
public import TernaryPeriodPolynomials.GroupCohomology.Relative.LeviCohomology

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open CategoryTheory CategoryTheory.Limits RelativeOrbitStabilizers RelativeExtObstruction

/-- Actual plane-stabilizer second cohomology vanishes in every even homogeneous degree. -/
theorem hp_H2_zero (n : ℕ) (hn : Even n) :
    IsZero (groupCohomology (Rep.res HP.subtype (coefficientRep n)) 2) :=
  actualPlane_H2_zero n hn RelativeLeviCohomology.plane_H2_zero

/-- Actual line-stabilizer second cohomology vanishes in every homogeneous degree. -/
theorem hl_H2_zero (n : ℕ) :
    IsZero (groupCohomology (Rep.res HL.subtype (coefficientRep n)) 2) :=
  actualLine_H2_zero n RelativeLeviCohomology.line_H2_zero

/-- Every genuine even-degree good-cycle polynomial morphism extends equivariantly to ordinary cycles. -/
theorem homogeneous_extension (n : ℕ) (hn : Even n)
    (f : GoodChainComplex.PolynomialCycleMap n 0) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ g c, F (OrdinaryIncidenceChains.complex.cyclesAction g c) =
        GoodChainComplex.coefficientAction n 0 g (F c)) ∧
      F.comp OrdinaryIncidenceChains.cycleInclusion = f.map :=
  homogeneous_extension_of_Levi n hn RelativeLeviCohomology.plane_H2_zero
    RelativeLeviCohomology.line_H2_zero f

end TernaryPoly.RelativeVertexCohomology
