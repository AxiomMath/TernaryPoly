module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeStabilizerEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Actual

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory HomologicalComplex IntegralGL3Congruence

/-- Genuine boundary local-system cochains are compared to both actual total models;
the comparison back to geometric cochains retains its specified cochain homotopy. -/
theorem actualBoundaryConeModels (W : Rep.{0} ℚ principalSix) :
    QuasiIso (localBoundaryToFaceTotal W) ∧
    QuasiIso (localBoundaryToStabilizerTotal W) ∧
    Nonempty (Homotopy (localBoundaryToStabilizerTotal W ≫ stabilizerTotalToGeometric W)
      (localBoundaryToFaceTotal W)) :=
  ⟨inferInstance,inferInstance,⟨localBoundaryStabilizerCompatibility W⟩⟩

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
