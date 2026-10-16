module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.RelativeVertexCohomologyActual
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.Cohomology

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open CategoryTheory CategoryTheory.Limits RelativeStabilizerParameters

/-- The genuine Ext–Shapiro extension needs only the actual Levi H² inputs after the vertex assembly. -/
theorem homogeneous_extension_of_Levi (n : ℕ) (hn : Even n)
    (hPlane : ∀ A : Rep ℚ GL2, IsZero (groupCohomology A 2))
    (hLine : ∀ A : Rep ℚ (ℤˣ × Gamma), IsZero (groupCohomology A 2))
    (f : GoodChainComplex.PolynomialCycleMap n 0) :
    ∃ F : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] PolynomialGLAction.HomogeneousPoly n,
      (∀ g c, F (OrdinaryIncidenceChains.complex.cyclesAction g c) =
        GoodChainComplex.coefficientAction n 0 g (F c)) ∧
      F.comp OrdinaryIncidenceChains.cycleInclusion = f.map :=
  RelativeEdgeCohomology.homogeneous_extension n hn
    (actualLine_H2_zero n hLine) (actualPlane_H2_zero n hn hPlane) f

end TernaryPoly.RelativeVertexCohomology
