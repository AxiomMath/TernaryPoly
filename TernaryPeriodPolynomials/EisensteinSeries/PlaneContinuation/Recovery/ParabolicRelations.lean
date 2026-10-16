module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ScalarRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryParabolicRelations

theorem frame_scalar (point : AdelicGL) (scalar : Adelesˣ) :
    frame (planeLevi 1 scalar * point) = frame point := by
  have equality := VectorGodementRelations.frame_levi_mul point 1 1 scalar
  simpa only [Units.val_one, Matrix.mul_one, inv_one, one_mul] using equality

theorem kernel_unipotent {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (first second : Adeles) (binary : BinaryAdelicGL) :
    RealBinaryRecovery.kernel induced (planeUnipotent first second * point) binary = RealBinaryRecovery.kernel induced point binary := by
  simp only [RealBinaryRecovery.kernel, VectorGodementRelations.frame_unipotent]

theorem kernel_scalar {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (scalar : Adelesˣ) (binary : BinaryAdelicGL) :
    RealBinaryRecovery.kernel induced (planeLevi 1 scalar * point) binary = RealBinaryRecovery.kernel induced point binary := by
  simp only [RealBinaryRecovery.kernel, frame_scalar]

theorem raw_unipotent {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (first second : Adeles) :
    FiniteRecoveryIntegral.sectionFunction induced (planeUnipotent first second * point) =
      FiniteRecoveryIntegral.sectionFunction induced point := by
  simp only [FiniteRecoveryIntegral.sectionFunction, kernel_unipotent, map_mul, det_planeUnipotent, one_mul]

theorem raw_scalar {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (scalar : Adelesˣ) :
    FiniteRecoveryIntegral.sectionFunction induced (planeLevi 1 scalar * point) =
      outerCharacter data parameter scalar * FiniteRecoveryIntegral.sectionFunction induced point := by
  simp only [FiniteRecoveryIntegral.sectionFunction, kernel_scalar, map_mul, det_planeLevi, map_one, one_mul, mul_assoc]

theorem section_unipotent {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (first second : Adeles) :
    FiniteSectionProjection.sectionFunction induced (planeUnipotent first second * point) =
      FiniteSectionProjection.sectionFunction induced point := by
  simp only [FiniteSectionProjection.sectionFunction, average, mul_assoc, raw_unipotent]

theorem section_scalar {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (scalar : Adelesˣ) :
    FiniteSectionProjection.sectionFunction induced (planeLevi 1 scalar * point) =
      outerCharacter data parameter scalar * FiniteSectionProjection.sectionFunction induced point := by
  simp only [FiniteSectionProjection.sectionFunction, average, mul_assoc, raw_scalar, ← Finset.mul_sum]
  ring

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryParabolicRelations
