module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.ParameterShift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.ParameterShiftHeight
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleParameterShift

def factor {degree : ℕ} (data : InducingData degree) (source target : ℂ) (realPoint : RealGL3) : ℂ :=
  (outerCharacter data target (GeneralLinearGroup.det (atInfinity realPoint)))⁻¹ *
    coefficient (target - source) (atInfinity realPoint) *
      outerCharacter data source (GeneralLinearGroup.det (atInfinity realPoint))

theorem factor_nonzero {degree : ℕ} (data : InducingData degree) (source target : ℂ) (realPoint : RealGL3) :
    factor data source target realPoint ≠ 0 :=
  mul_ne_zero (mul_ne_zero (inv_ne_zero (character_ne_zero _ _)) (coefficient_nonzero _ _)) (character_ne_zero _ _)

theorem coefficient_integral (difference : ℂ) (point : IntegralFiniteGL) (realPoint : RealGL3) :
    coefficient difference (inclusion point * atInfinity realPoint) = coefficient difference (atInfinity realPoint) := by
  change coefficient difference (atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint) = _
  rw [atFinite_atInfinity_commute]
  exact coefficient_compact difference _ _ (MaximalCompact.finiteCompact_atFinite ⟨_, point, rfl⟩)

theorem normalized_shift {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (original : IsInduced data .plane source value) (target : ℂ) (point : IntegralFiniteGL) (realPoint : RealGL3) :
    normalized (InducedParameterShift.induced original target) (inclusion point * atInfinity realPoint) =
      factor data source target realPoint • normalized original (inclusion point * atInfinity realPoint) := by
  rw [normalized, InducedParameterShift.cuspVector original target
    (inclusion point * atInfinity realPoint), normalized, smul_smul, smul_smul]
  apply congrArg (fun scalar : ℂ => scalar • planeCuspVector original (inclusion point * atInfinity realPoint))
  have outer_source : outerCharacter data source (GeneralLinearGroup.det (inclusion point)) =
      FiniteProfileResidues.character data point := RecoveryLevel.outer_integral data source point
  have outer_target : outerCharacter data target (GeneralLinearGroup.det (inclusion point)) =
      FiniteProfileResidues.character data point := RecoveryLevel.outer_integral data target point
  simp only [map_mul, outer_source, outer_target, coefficient_integral, factor]
  field_simp [FiniteProfileResidues.character_nonzero data point, character_ne_zero (outerCharacter data source) _,
    character_ne_zero (outerCharacter data target) _]

theorem tuple_shift {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (original : IsInduced data .plane source value) (target : ℂ) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ProfileTuples.tuple (InducedParameterShift.induced original target) frame =
      factor data source target (RealFrameChart.point frame) • ProfileTuples.tuple original frame := by
  funext key
  change (FrameProfile.profile (InducedParameterShift.induced original target)
    (RealFrameChart.adelicFrame (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key)) frame)).val = _
  rw [RealFrameChart.profile_eq _ _ frame fullRank]
  change (normalized (InducedParameterShift.induced original target)
    (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity (RealFrameChart.point frame))).val = _
  rw [normalized_shift]
  change factor data source target (RealFrameChart.point frame) •
    (normalized original (inclusion (UniversalFiniteProfiles.representative data key) * atInfinity (RealFrameChart.point frame))).val = _
  exact congrArg (fun vector : data.cusp.smooth => factor data source target (RealFrameChart.point frame) • vector.val)
    (RealFrameChart.profile_eq original _ frame fullRank).symm

theorem tuple_mem_parameter {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (original : IsInduced data .plane source value) (target : ℂ) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ProfileTuples.tuple original frame ∈ TupleInducedRecovery.admissible data target := by
  have scaled := (TupleInducedRecovery.admissible data target).smul_mem
    (factor data source target (RealFrameChart.point frame))⁻¹
    (TupleInducedRecovery.tuple_mem (InducedParameterShift.induced original target) frame fullRank)
  rw [tuple_shift original target frame fullRank, inv_smul_smul₀ (factor_nonzero data source target _)] at scaled
  exact scaled

theorem admissible_eq {degree : ℕ} (data : InducingData degree) (parameter : ℂ) :
    TupleInducedRecovery.admissible data parameter = ProfileTuples.admissible data := by
  apply le_antisymm (TupleInducedRecovery.admissible_le data parameter)
  apply (Submodule.span ℂ (ProfileTuples.generators data)).topologicalClosure_minimal _
    (TupleInducedRecovery.admissible_closed data parameter)
  apply Submodule.span_le.mpr
  rintro _ ⟨source, value, original, frame, fullRank, rfl⟩
  exact tuple_mem_parameter original parameter frame fullRank

theorem operator_preserves {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (value : ProfileTuples.Space data)
    (membership : value ∈ ProfileTuples.admissible data) :
    TupleRecoveryOperator.operator data parameter halfPlane value ∈ ProfileTuples.admissible data := by
  rw [← admissible_eq data parameter] at membership ⊢
  exact TupleInducedRecovery.operator_preserves data parameter halfPlane value membership

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleParameterShift
