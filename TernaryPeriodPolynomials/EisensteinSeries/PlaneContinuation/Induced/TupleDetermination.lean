module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ParameterShift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedTupleDetermination

theorem cuspVector_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second)
    (equalities : ∀ frame : Rectangular ℝ, FullRank frame →
      ProfileTuples.tuple firstInduced frame = ProfileTuples.tuple secondInduced frame)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    planeCuspVector firstInduced (inclusion point * atInfinity realPoint) =
      planeCuspVector secondInduced (inclusion point * atInfinity realPoint) := by
  let frame := realFrame (atInfinity realPoint)
  have fullRank : FullRank frame := realFrame_fullRank _
  have profileEquality : profile firstInduced (RealFrameChart.adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) frame) =
      profile secondInduced (RealFrameChart.adelicFrame (Matrix.GeneralLinearGroup.map integralEmbedding point) frame) := by
    apply Subtype.ext
    exact (ProfileTuples.profile_selected firstInduced point frame fullRank).symm.trans
      ((congrFun (equalities frame fullRank) (UniversalFiniteProfiles.selected data point)).trans
        (ProfileTuples.profile_selected secondInduced point frame fullRank))
  rw [TupleRealCovariance.profile_realPoint firstInduced point realPoint,
    TupleRealCovariance.profile_realPoint secondInduced point realPoint] at profileEquality
  change (outerCharacter data parameter (Matrix.GeneralLinearGroup.det (inclusion point * atInfinity realPoint)))⁻¹ •
      planeCuspVector firstInduced (inclusion point * atInfinity realPoint) =
    (outerCharacter data parameter (Matrix.GeneralLinearGroup.det (inclusion point * atInfinity realPoint)))⁻¹ •
      planeCuspVector secondInduced (inclusion point * atInfinity realPoint) at profileEquality
  exact (smul_right_inj (inv_ne_zero (FrameProfile.character_ne_zero _ _))).mp profileEquality

theorem ext {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {first second : AdelicGL → ℂ} (firstInduced : IsInduced data .plane parameter first)
    (secondInduced : IsInduced data .plane parameter second)
    (equalities : ∀ frame : Rectangular ℝ, FullRank frame →
      ProfileTuples.tuple firstInduced frame = ProfileTuples.tuple secondInduced frame) : first = second := by
  funext point
  obtain ⟨a, b, binary, scalar, integer, realPoint, equality⟩ := RecoveryGlobalCusp.point_factorization point
  rw [equality, firstInduced.2.2.2.1, secondInduced.2.2.2.1, Helpers.planeLevi_split, mul_assoc,
    firstInduced.2.2.2.2.1, secondInduced.2.2.2.2.1,
    induced_eq_planeCuspVector firstInduced, induced_eq_planeCuspVector secondInduced,
    cuspVector_eq firstInduced secondInduced equalities integer realPoint]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedTupleDetermination
