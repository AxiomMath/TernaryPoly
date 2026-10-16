module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.FiniteCusp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRealCovariance

theorem normalized_levi {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (binary : BinaryRealGL) :
    normalized induced (planeLevi (atInfinity binary) 1 * point) =
      innerCharacter data parameter (GeneralLinearGroup.det (atInfinity binary)) •
        DirectionalRealization.smoothTranslate data.cusp binary (normalized induced point) := by
  apply Subtype.ext
  simp only [normalized, CuspVectors.planeCuspVector_binaryLevi, map_mul, det_planeLevi, mul_one,
    Submodule.coe_smul, DirectionalRealization.smoothTranslate, LinearMap.coe_mk, AddHom.coe_mk, map_smul, smul_smul]
  apply congrArg (fun scalar : ℂ => scalar • data.cusp.π (atInfinity binary) (CuspVectors.planeCuspVector induced point).val)
  rw [← characters_product data parameter (GeneralLinearGroup.det (atInfinity binary))]
  field_simp [FrameProfile.character_ne_zero (outerCharacter data parameter) (GeneralLinearGroup.det point),
    FrameProfile.character_ne_zero (outerCharacter data parameter) (GeneralLinearGroup.det (atInfinity binary))]

theorem profile_realPoint {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : IntegralFiniteGL) (realPoint : RealGL3) :
    profile induced (RealFrameChart.adelicFrame (GeneralLinearGroup.map integralEmbedding point)
      (realFrame (atInfinity realPoint))) = normalized induced (inclusion point * atInfinity realPoint) := by
  have finitePart : finiteGroup (inclusion point * atInfinity realPoint) = GeneralLinearGroup.map integralEmbedding point := by
    rw [map_mul]
    change GeneralLinearGroup.map integralEmbedding point * 1 = _
    exact mul_one _
  have frames := frame_eq (inclusion point * atInfinity realPoint)
  rw [finitePart, TupleSectionRealization.realFrame_integral] at frames
  rw [← frames, profile_frame]

theorem point_levi (point : IntegralFiniteGL) (realPoint : RealGL3) (binary : BinaryRealGL) :
    inclusion point * atInfinity (planeLevi binary 1 * realPoint) =
      planeLevi (atInfinity binary) 1 * (inclusion point * atInfinity realPoint) := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, ← OrbitSmooth.planeLevi_atInfinity, ← mul_assoc]
  change atFinite (GeneralLinearGroup.map integralEmbedding point) * planeLevi (atInfinity binary) 1 * atInfinity realPoint = _
  rw [OrbitSmooth.planeLevi_atInfinity, atFinite_atInfinity_commute, mul_assoc]
  rfl

theorem vectors_levi {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (realPoint : RealGL3) (binary : BinaryRealGL) :
    ProfileTuples.vectors induced (realFrame (atInfinity (planeLevi binary 1 * realPoint))) =
      innerCharacter data parameter (GeneralLinearGroup.det (atInfinity binary)) •
        SmoothTupleOperator.realAction data binary (ProfileTuples.vectors induced (realFrame (atInfinity realPoint))) := by
  funext key
  change profile induced (RealFrameChart.adelicFrame
    (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key))
      (realFrame (atInfinity (planeLevi binary 1 * realPoint)))) =
    innerCharacter data parameter (GeneralLinearGroup.det (atInfinity binary)) •
      DirectionalRealization.smoothTranslate data.cusp binary
        (profile induced (RealFrameChart.adelicFrame
          (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key))
            (realFrame (atInfinity realPoint))))
  rw [profile_realPoint induced, profile_realPoint induced, point_levi, normalized_levi]

theorem averagedRow_levi {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) (binary : BinaryRealGL) :
    SmoothTupleOperator.averagedRow data parameter halfPlane point
      (ProfileTuples.vectors induced (realFrame (atInfinity (planeLevi binary 1 * realPoint)))) =
        innerCharacter data parameter (GeneralLinearGroup.det (atInfinity binary)) •
          DirectionalRealization.smoothTranslate data.cusp binary
            (SmoothTupleOperator.averagedRow data parameter halfPlane point
              (ProfileTuples.vectors induced (realFrame (atInfinity realPoint)))) := by
  rw [vectors_levi, map_smul, SmoothTupleOperator.averagedRow_real]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleRealCovariance
