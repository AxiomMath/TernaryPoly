module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.SectionRealization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleFiniteCusp

theorem levi_inverse (binary : BinaryAdelicGL) : planeLevi binary⁻¹ 1 * planeLevi binary 1 = 1 := by
  change (planeLeviHom Adeles) (binary⁻¹, 1) * (planeLeviHom Adeles) (binary, 1) = 1
  rw [← map_mul]
  change (planeLeviHom Adeles) (binary⁻¹ * binary, (1 : Adelesˣ) * 1) = 1
  rw [inv_mul_cancel, one_mul]
  exact (planeLeviHom Adeles).map_one

theorem coefficient_levi {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : AdelicGL)
    (matrix : BinaryFiniteGL) (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL) :
    RecoveryCoefficients.coefficient data parameter (planeLevi (atFinite matrix) 1 * point) key (matrix * binary) =
      innerCharacter data parameter (GeneralLinearGroup.det (atFinite matrix)) *
        RecoveryCoefficients.coefficient data parameter point key binary := by
  rw [RecoveryBinarySymmetry.coefficient_left, ← mul_assoc, levi_inverse, one_mul]

theorem realFrame_levi (point : AdelicGL) (matrix : BinaryFiniteGL) :
    realFrame (planeLevi (atFinite matrix) 1 * point) = realFrame point := by
  rw [planeLevi_atFinite, realFrame, map_mul]
  have identity : realGroup (atFinite (planeLevi matrix 1)) = 1 := by apply Units.ext; rfl
  rw [identity, one_mul]
  rfl

theorem raw_integral {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryFiniteGL) :
    (∫ binary : BinaryFiniteGL,
      RealBinaryRecovery.kernel induced (planeLevi (atFinite evaluation) 1 * (inclusion point * atInfinity realPoint))
        (atFinite binary) ∂BinaryProductHaar.finiteMeasure) =
      innerCharacter data parameter (GeneralLinearGroup.det (atFinite evaluation)) *
        TupleScalarAverage.raw data parameter point (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))) (atFinite evaluation) := by
  rw [← integral_mul_left_eq_self (μ := BinaryProductHaar.finiteMeasure)
    (fun binary => RealBinaryRecovery.kernel induced
      (planeLevi (atFinite evaluation) 1 * (inclusion point * atInfinity realPoint)) (atFinite binary)) evaluation]
  simp_rw [RecoveryCoefficients.kernel_eq]
  simp_rw [coefficient_levi]
  simp only [realFrame_levi, TupleSectionRealization.realFrame_integral,
    PrimitiveTupleKernel.coefficient_infinity, atFinite_mul, mul_assoc, ← Finset.mul_sum]
  rw [integral_const_mul]
  apply congrArg (fun scalar : ℂ => innerCharacter data parameter (GeneralLinearGroup.det (atFinite evaluation)) * scalar)
  change (∫ binary, ∑ key, RecoveryCoefficients.coefficient data parameter
    (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary *
      data.cusp.realize (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)) key)
        (atFinite evaluation * atFinite binary) ∂BinaryProductHaar.finiteMeasure) =
    ∑ key, ∫ binary, RecoveryCoefficients.coefficient data parameter
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary *
        data.cusp.realize (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)) key)
          (atFinite evaluation * atFinite binary) ∂BinaryProductHaar.finiteMeasure
  apply integral_finsetSum Finset.univ
  intro key _
  exact TupleSectionRealization.scalar_integrable data.cusp _ _
    (RecoveryCoefficients.coefficient_integrable data parameter halfPlane
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) (atFinite evaluation)

theorem raw_section {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryFiniteGL) :
    FiniteRecoveryIntegral.sectionFunction induced
      (planeLevi (atFinite evaluation) 1 * (inclusion point * atInfinity realPoint)) =
      normPower (GeneralLinearGroup.det (atFinite evaluation)) (binaryInductionExponent degree .plane parameter) *
        (outerCharacter data parameter (GeneralLinearGroup.det (atInfinity realPoint)) *
          TupleScalarAverage.sectionRow data parameter point
            (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))) (atFinite evaluation)) := by
  rw [FiniteRecoveryIntegral.sectionFunction, raw_integral induced halfPlane point realPoint evaluation]
  simp only [map_mul, det_planeLevi, mul_one]
  have outer : outerCharacter data parameter (GeneralLinearGroup.det (inclusion point)) =
      FiniteProfileResidues.character data point := RecoveryLevel.outer_integral data parameter point
  rw [outer, TupleScalarAverage.sectionRow]
  rw [← characters_product data parameter (GeneralLinearGroup.det (atFinite evaluation))]
  ring

theorem averaged_section {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryFiniteGL) :
    FiniteSectionProjection.sectionFunction induced
      (planeLevi (atFinite evaluation) 1 * (inclusion point * atInfinity realPoint)) =
      normPower (GeneralLinearGroup.det (atFinite evaluation)) (binaryInductionExponent degree .plane parameter) *
        (outerCharacter data parameter (GeneralLinearGroup.det (atInfinity realPoint)) *
          TupleScalarAverage.average data parameter point
            (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))) (atFinite evaluation)) := by
  have product (matrix : IntegralFiniteGL) :
      (planeLevi (atFinite evaluation) 1 * (inclusion point * atInfinity realPoint)) * inclusion matrix =
        planeLevi (atFinite evaluation) 1 * (inclusion (point * matrix) * atInfinity realPoint) := by
    rw [mul_assoc]
    apply congrArg (fun g : AdelicGL => planeLevi (atFinite evaluation) 1 * g)
    change (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint) *
      atFinite (GeneralLinearGroup.map integralEmbedding matrix) = _
    rw [mul_assoc, ← atFinite_atInfinity_commute, ← mul_assoc, ← atFinite_mul, ← map_mul]
    rfl
  simp only [FiniteSectionProjection.sectionFunction, FiniteSectionProjection.average, product,
    raw_section induced halfPlane, TupleScalarAverage.average, ← Finset.mul_sum]
  ring

theorem section_realize {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (evaluation : BinaryFiniteGL) :
    FiniteSectionProjection.sectionFunction induced
      (planeLevi (atFinite evaluation) 1 * (inclusion point * atInfinity realPoint)) =
      normPower (GeneralLinearGroup.det (atFinite evaluation)) (binaryInductionExponent degree .plane parameter) *
        (outerCharacter data parameter (GeneralLinearGroup.det (inclusion point * atInfinity realPoint)) *
          data.cusp.realize (SmoothTupleOperator.averagedRow data parameter halfPlane point
            (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)))) (atFinite evaluation)) := by
  rw [TupleScalarAverage.averagedRow_realize data parameter halfPlane point
    (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)))
    (fun key => ProfileTuples.profile_fixed induced (UniversalFiniteProfiles.representative data key)
      (realFrame (atInfinity realPoint)) (realFrame_fullRank (atInfinity realPoint))) (atFinite evaluation),
    averaged_section induced halfPlane point realPoint evaluation]
  simp only [map_mul]
  have outer : outerCharacter data parameter (GeneralLinearGroup.det (inclusion point)) =
      FiniteProfileResidues.character data point := RecoveryLevel.outer_integral data parameter point
  rw [outer]
  field_simp [FiniteProfileResidues.character_nonzero data point]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleFiniteCusp
