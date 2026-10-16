module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalInducedVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalParabolicParameters

@[expose] public section


open CategoryTheory
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open LowDegreeHochschildSerre

/-- Two actual derived congruence transvections suffice for the full parabolic's radical H¹. -/
theorem actualPlane_radical_H1_stepThree_fixed_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (actualPlaneRadicalRep n e) 1)
    (hu : (cohomologyRep OrdinaryParabolicGroups.planeAction
      (Rep.of (OrdinaryParabolicGroups.planeCoefficients n e)) 1).ρ (binaryUpperStep 3,1) x=x)
    (hl : (cohomologyRep OrdinaryParabolicGroups.planeAction
      (Rep.of (OrdinaryParabolicGroups.planeCoefficients n e)) 1).ρ (binaryLowerStep 3,1) x=x) : x=0 := by
  have hi : Function.Injective (inducedPlaneParameterIso n e).inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hi
  rw [map_zero]
  apply inducedPlaneH1_stepThree_fixed_zero
  · rw [←inducedPlaneParameterIso_natural,hu]
  · rw [←inducedPlaneParameterIso_natural,hl]

/-- The actual line radical has the same two-transvection detection in every coefficient degree. -/
theorem actualLine_radical_H1_stepThree_fixed_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (actualLineRadicalRep n e) 1)
    (hu : (cohomologyRep OrdinaryParabolicGroups.lineAction
      (Rep.of (OrdinaryParabolicGroups.lineCoefficients n e)) 1).ρ (1,binaryUpperStep 3) x=x)
    (hl : (cohomologyRep OrdinaryParabolicGroups.lineAction
      (Rep.of (OrdinaryParabolicGroups.lineCoefficients n e)) 1).ρ (1,binaryLowerStep 3) x=x) : x=0 := by
  have hi : Function.Injective (inducedLineParameterIso n e).inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hi
  rw [map_zero]
  apply inducedLineH1_stepThree_fixed_zero
  · rw [←inducedLineParameterIso_natural,hu]
  · rw [←inducedLineParameterIso_natural,hl]

/-- The exact actual Levi-fixed radical H¹ gate for plane-face inflation, with no degree restriction. -/
theorem actualPlane_radical_H1_invariants_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (radicalRep OrdinaryParabolicGroups.planeAction
      (Rep.of (OrdinaryParabolicGroups.planeCoefficients n e))) 1)
    (hx : ∀ q,(cohomologyRep OrdinaryParabolicGroups.planeAction
      (Rep.of (OrdinaryParabolicGroups.planeCoefficients n e)) 1).ρ q x=x) : x=0 :=
  actualPlane_radical_H1_stepThree_fixed_zero n e x (hx _) (hx _)

/-- The exact actual Levi-fixed radical H¹ gate for line-face inflation, with every twist retained. -/
theorem actualLine_radical_H1_invariants_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (radicalRep OrdinaryParabolicGroups.lineAction
      (Rep.of (OrdinaryParabolicGroups.lineCoefficients n e))) 1)
    (hx : ∀ q,(cohomologyRep OrdinaryParabolicGroups.lineAction
      (Rep.of (OrdinaryParabolicGroups.lineCoefficients n e)) 1).ρ q x=x) : x=0 :=
  actualLine_radical_H1_stepThree_fixed_zero n e x (hx _) (hx _)

end TernaryPoly.OrdinaryFaceRadical
