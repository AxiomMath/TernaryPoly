module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.CuspLift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleCuspRegularity

def diagonal {degree : ℕ} (data : InducingData degree) : ProfileTuples.Space data →L[ℂ] ProfileTuples.Space data :=
  ContinuousLinearMap.pi (fun key =>
    (FiniteProfileResidues.character data (UniversalFiniteProfiles.representative data key))⁻¹ • ContinuousLinearMap.proj key)

def operator {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (point : IntegralFiniteGL) : ProfileTuples.Space data →L[ℂ] data.cusp.H :=
  FiniteProfileResidues.character data point •
    (TupleRecoveryOperator.averagedRow data parameter halfPlane point).comp (diagonal data)

theorem vectors_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (realPoint : RealGL3) :
    ProfileTuples.vectors induced (realFrame (atInfinity realPoint)) =
      (outerCharacter data parameter (GeneralLinearGroup.det (atInfinity realPoint)))⁻¹ •
        (fun key => (FiniteProfileResidues.character data (UniversalFiniteProfiles.representative data key))⁻¹ •
          planeCuspVector induced (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity realPoint)) := by
  funext key
  change profile induced _ = _
  rw [TupleRealCovariance.profile_realPoint induced, normalized, map_mul, map_mul, mul_inv]
  change ((outerCharacter data parameter (GeneralLinearGroup.det
    (atFinite (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key)))))⁻¹ * _) • _ = _
  rw [RecoveryLevel.outer_integral, mul_smul, smul_comm]
  rfl

theorem vector_val {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    (TupleCuspLift.vector induced halfPlane point realPoint).val =
      operator data parameter halfPlane point (fun key =>
        (planeCuspVector induced (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity realPoint)).val) := by
  rw [TupleCuspLift.vector, vectors_eq induced realPoint, map_smul]
  simp only [Submodule.coe_smul, SmoothTupleOperator.averagedRow_val, map_mul]
  change (outerCharacter data parameter (GeneralLinearGroup.det
    (atFinite (GeneralLinearGroup.map integralEmbedding point))) * _) • (_ • _) = _
  rw [RecoveryLevel.outer_integral, ← smul_smul,
    smul_inv_smul₀ (FrameProfile.character_ne_zero (outerCharacter data parameter)
      (GeneralLinearGroup.det (atInfinity realPoint)))]
  rfl

theorem vector_smooth {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    Smooth (fun matrices : Fin 1 → RealGL3 => (TupleCuspLift.vector induced halfPlane point (realPoint * matrices 0)).val) := by
  simp only [vector_val, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
  apply ((operator data parameter halfPlane point).restrictScalars ℝ).contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro key
  simpa only [Smooth, mul_assoc] using planeCuspVector_smooth induced
    (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity realPoint)

theorem exists_smooth_lift {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    ∃ lift : (Fin 1 → RealGL3) → data.cusp.smooth,
      Smooth (fun matrices => (lift matrices).val) ∧
        ∀ matrices evaluation, data.cusp.realize (lift matrices) evaluation =
          normPower (GeneralLinearGroup.det evaluation) (-binaryInductionExponent degree .plane parameter) *
            FiniteSectionProjection.sectionFunction induced
              (planeLevi evaluation 1 * ((inclusion point * atInfinity realPoint) * atInfinity (matrices 0))) := by
  refine ⟨fun matrices => TupleCuspLift.vector induced halfPlane point (realPoint * matrices 0),
    vector_smooth induced halfPlane point realPoint, ?_⟩
  intro matrices evaluation
  simp only [TupleCuspLift.realize_vector, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, mul_assoc]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleCuspRegularity
