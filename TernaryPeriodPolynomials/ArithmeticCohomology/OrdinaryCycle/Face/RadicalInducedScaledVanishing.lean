module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalInducedActions
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalFiberCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalScaledTransvections

@[expose] public section

open CategoryTheory
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open OrdinaryBoundaryCommonRoot OrdinaryCovectors

/-- Every step-three plane-radical H¹ class in the actual induced coefficient module fixed by
the two actual derived congruence transvections is zero, for every determinant exponent. -/
theorem scaledInducedPlaneH1_stepThree_fixed_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (scaledInducedPlaneRep n e) 1)
    (hu : scaledInducedPlaneH1Action n e (binaryUpperStep 3) x=x)
    (hl : scaledInducedPlaneH1Action n e (binaryLowerStep 3) x=x) : x=0 := by
  apply fiberH1_jointly_injective (scaledInducedPlaneRep n e).ρ (scaledPlaneRep n).ρ
    (scaledPlaneFiberAction n e) x
  intro r
  apply scaledPlaneH1_stepThree_fixed_zero
  · have h := fiberH1Map_natural (scaledInducedPlaneRep n e).ρ (scaledPlaneRep n).ρ
      (scaledPlaneFiberAction n e) _ (scaledInducedPlaneCoefficientHom n e (binaryUpperStep 3))
      (scaledPlaneCoefficientHom n (binaryUpperStep 3)) r
      (scaledInducedPlaneCoefficient_fiber n e _ planeUpperThree_reduction (planeUpperStep_det 3) r) x
    change fiberH1Map _ _ _ r (scaledInducedPlaneH1Action n e (binaryUpperStep 3) x)=
      scaledPlaneH1Action n (binaryUpperStep 3) (fiberH1Map _ _ _ r x) at h
    rw [hu] at h
    exact h.symm
  · have h := fiberH1Map_natural (scaledInducedPlaneRep n e).ρ (scaledPlaneRep n).ρ
      (scaledPlaneFiberAction n e) _ (scaledInducedPlaneCoefficientHom n e (binaryLowerStep 3))
      (scaledPlaneCoefficientHom n (binaryLowerStep 3)) r
      (scaledInducedPlaneCoefficient_fiber n e _ planeLowerThree_reduction (planeLowerStep_det 3) r) x
    change fiberH1Map _ _ _ r (scaledInducedPlaneH1Action n e (binaryLowerStep 3) x)=
      scaledPlaneH1Action n (binaryLowerStep 3) (fiberH1Map _ _ _ r x) at h
    rw [hl] at h
    exact h.symm

/-- The analogous actual induced-module statement for the complete step-three line radical. -/
theorem scaledInducedLineH1_stepThree_fixed_zero (n : ℕ) (e : ℤ)
    (x : groupCohomology (scaledInducedLineRep n e) 1)
    (hu : scaledInducedLineH1Action n e 1 (binaryUpperStep 3) x=x)
    (hl : scaledInducedLineH1Action n e 1 (binaryLowerStep 3) x=x) : x=0 := by
  apply fiberH1_jointly_injective (scaledInducedLineRep n e).ρ (scaledLineRep n).ρ
    (scaledLineFiberAction n e) x
  intro r
  apply scaledLineH1_stepThree_fixed_zero
  · have h := fiberH1Map_natural (scaledInducedLineRep n e).ρ (scaledLineRep n).ρ
      (scaledLineFiberAction n e) _ (scaledInducedLineCoefficientHom n e 1 (binaryUpperStep 3))
      (scaledLineCoefficientHom n 1 (binaryUpperStep 3)) r
      (scaledInducedLineCoefficient_fiber n e 1 _ lineUpperThree_reduction (lineUpperStep_det 3) r) x
    change fiberH1Map _ _ _ r (scaledInducedLineH1Action n e 1 (binaryUpperStep 3) x)=
      scaledLineH1Action n 1 (binaryUpperStep 3) (fiberH1Map _ _ _ r x) at h
    rw [hu] at h
    exact h.symm
  · have h := fiberH1Map_natural (scaledInducedLineRep n e).ρ (scaledLineRep n).ρ
      (scaledLineFiberAction n e) _ (scaledInducedLineCoefficientHom n e 1 (binaryLowerStep 3))
      (scaledLineCoefficientHom n 1 (binaryLowerStep 3)) r
      (scaledInducedLineCoefficient_fiber n e 1 _ lineLowerThree_reduction (lineLowerStep_det 3) r) x
    change fiberH1Map _ _ _ r (scaledInducedLineH1Action n e 1 (binaryLowerStep 3) x)=
      scaledLineH1Action n 1 (binaryLowerStep 3) (fiberH1Map _ _ _ r x) at h
    rw [hl] at h
    exact h.symm

end TernaryPoly.OrdinaryFaceRadical
