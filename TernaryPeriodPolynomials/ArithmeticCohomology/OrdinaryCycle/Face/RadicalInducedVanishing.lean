module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalInducedScaledVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalInducedRestriction
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.StepThreeRestriction

@[expose] public section


open CategoryTheory
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical

/-- Actual full plane-radical H¹ vanishes under the two derived congruence transvections,
for the induced twenty-six-fiber coefficient module and every integer determinant twist. -/
theorem inducedPlaneH1_stepThree_fixed_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (Rep.of (inducedPlaneRepresentation n e)) 1)
    (hu : inducedPlaneH1Action n e (binaryUpperStep 3) x=x)
    (hl : inducedPlaneH1Action n e (binaryLowerStep 3) x=x) : x=0 := by
  apply (scaleLattice_three_restriction_zero_iff (Rep.of (inducedPlaneRepresentation n e)) 1 x).mp
  change inducedPlaneRestriction n e x=0
  apply scaledInducedPlaneH1_stepThree_fixed_zero
  · rw [←inducedPlaneRestriction_natural,hu]
  · rw [←inducedPlaneRestriction_natural,hl]

/-- Actual full line-radical H¹ vanishes under the same two derived congruence transvections,
with every integer determinant exponent retained. -/
theorem inducedLineH1_stepThree_fixed_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (Rep.of (inducedLineRepresentation n e)) 1)
    (hu : inducedLineH1Action n e 1 (binaryUpperStep 3) x=x)
    (hl : inducedLineH1Action n e 1 (binaryLowerStep 3) x=x) : x=0 := by
  apply (scaleLattice_three_restriction_zero_iff (Rep.of (inducedLineRepresentation n e)) 1 x).mp
  change inducedLineRestriction n e x=0
  apply scaledInducedLineH1_stepThree_fixed_zero
  · rw [←inducedLineRestriction_natural,hu]
  · rw [←inducedLineRestriction_natural,hl]

end TernaryPoly.OrdinaryFaceRadical
