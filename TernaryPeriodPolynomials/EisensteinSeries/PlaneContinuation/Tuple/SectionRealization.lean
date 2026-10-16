module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ScalarAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleSectionRealization

theorem scalar_integrable (data : CuspidalRepresentation) (vector : data.smooth)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (evaluation : BinaryAdelicGL) :
    Integrable (fun binary => coefficient binary * data.realize vector (evaluation * atFinite binary))
      BinaryProductHaar.finiteMeasure := by
  apply (integrable.norm.mul_const (CuspSupNorm.cuspSupNorm vector)).mono'
    (integrable.aestronglyMeasurable.mul
      ((CuspFunctionContinuity.continuous data vector).comp
        (continuous_const.mul FiniteHilbertConvolution.atFinite_continuous)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun binary => by
    change ‖coefficient binary * data.realize vector (evaluation * atFinite binary)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (CuspSupNorm.realize_le_cuspSupNorm vector _) (norm_nonneg _))

theorem realFrame_integral (point : IntegralFiniteGL) (realPoint : RealGL3) :
    realFrame (inclusion point * atInfinity realPoint) = realFrame (atInfinity realPoint) := by
  change realFrame (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint) = _
  rw [atFinite_atInfinity_commute, RecoveryLevel.realFrame_right]

theorem raw_integral {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    TupleScalarAverage.raw data parameter point (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))) 1 =
      ∫ binary : BinaryFiniteGL, RealBinaryRecovery.kernel induced (inclusion point * atInfinity realPoint) (atFinite binary)
        ∂BinaryProductHaar.finiteMeasure := by
  simp only [RecoveryCoefficients.kernel_eq, realFrame_integral, PrimitiveTupleKernel.coefficient_infinity]
  symm
  change (∫ binary, ∑ key, RecoveryCoefficients.coefficient data parameter
    (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary *
      data.cusp.realize (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)) key) (atFinite binary)
        ∂BinaryProductHaar.finiteMeasure) =
    ∑ key, ∫ binary, RecoveryCoefficients.coefficient data parameter
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) key binary *
        data.cusp.realize (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)) key) (1 * atFinite binary)
          ∂BinaryProductHaar.finiteMeasure
  simp only [one_mul]
  apply integral_finsetSum Finset.univ
  intro key _
  simpa only [one_mul] using scalar_integrable data.cusp (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)) key) _
    (RecoveryCoefficients.coefficient_integrable data parameter halfPlane
      (atFinite (GeneralLinearGroup.map integralEmbedding point)) ⟨point, rfl⟩ key) 1

theorem raw_section {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    FiniteRecoveryIntegral.sectionFunction induced (inclusion point * atInfinity realPoint) =
      outerCharacter data parameter (GeneralLinearGroup.det (atInfinity realPoint)) *
        TupleScalarAverage.sectionRow data parameter point (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))) 1 := by
  rw [FiniteRecoveryIntegral.sectionFunction, ← raw_integral induced halfPlane point realPoint,
    map_mul, map_mul]
  change (outerCharacter data parameter (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding point))) * _) * _ = _
  rw [RecoveryLevel.outer_integral, TupleScalarAverage.sectionRow]
  ring

theorem averaged_section {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    FiniteSectionProjection.sectionFunction induced (inclusion point * atInfinity realPoint) =
      outerCharacter data parameter (GeneralLinearGroup.det (atInfinity realPoint)) *
        TupleScalarAverage.average data parameter point (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))) 1 := by
  have product (matrix : IntegralFiniteGL) :
      (inclusion point * atInfinity realPoint) * inclusion matrix = inclusion (point * matrix) * atInfinity realPoint := by
    change (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint) *
      atFinite (GeneralLinearGroup.map integralEmbedding matrix) = _
    rw [mul_assoc, ← atFinite_atInfinity_commute, ← mul_assoc, ← atFinite_mul, ← map_mul]
    rfl
  simp only [FiniteSectionProjection.sectionFunction, FiniteSectionProjection.average, product,
    raw_section induced halfPlane, TupleScalarAverage.average, ← Finset.mul_sum]
  ring

theorem section_realize {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    FiniteSectionProjection.sectionFunction induced (inclusion point * atInfinity realPoint) =
      outerCharacter data parameter (GeneralLinearGroup.det (inclusion point * atInfinity realPoint)) *
        data.cusp.realize (SmoothTupleOperator.averagedRow data parameter halfPlane point
          (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)))) 1 := by
  rw [TupleScalarAverage.averagedRow_realize data parameter halfPlane point
    (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)))
    (fun key => ProfileTuples.profile_fixed induced (UniversalFiniteProfiles.representative data key)
      (realFrame (atInfinity realPoint)) (realFrame_fullRank (atInfinity realPoint))) 1]
  rw [averaged_section induced halfPlane point realPoint, map_mul, map_mul]
  change _ = (outerCharacter data parameter (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding point))) * _) * _
  rw [RecoveryLevel.outer_integral]
  field_simp [FiniteProfileResidues.character_nonzero data point]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleSectionRealization
