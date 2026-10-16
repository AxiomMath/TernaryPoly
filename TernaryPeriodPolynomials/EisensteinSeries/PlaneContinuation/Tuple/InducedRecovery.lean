module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.GlobalCusp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSectionProjection TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleInducedRecovery

theorem cuspVector {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (realPoint : RealGL3) :
    planeCuspVector (RecoveryGlobalCusp.section_induced induced halfPlane) (inclusion point * atInfinity realPoint) =
      TupleCuspLift.vector induced halfPlane point realPoint := by
  apply planeCuspVector_unique
  intro evaluation
  exact TupleCuspLift.realize_vector induced halfPlane point realPoint evaluation

theorem realFrame_point (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    realFrame (atInfinity (RealFrameChart.point frame)) = frame := by
  have equality := PrimitiveTupleKernel.realFrame_chart (1 : FiniteGL) frame fullRank
  simpa only [CompactAveraging.atFinite_one, one_mul] using equality

theorem profile {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (point : IntegralFiniteGL) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    FrameProfile.profile (RecoveryGlobalCusp.section_induced induced halfPlane)
      (RealFrameChart.adelicFrame (GeneralLinearGroup.map integralEmbedding point) frame) =
        SmoothTupleOperator.averagedRow data parameter halfPlane point (ProfileTuples.vectors induced frame) := by
  rw [RealFrameChart.profile_eq _ _ frame fullRank]
  change normalized (RecoveryGlobalCusp.section_induced induced halfPlane) (inclusion point * atInfinity (RealFrameChart.point frame)) = _
  rw [normalized, cuspVector induced halfPlane point (RealFrameChart.point frame), TupleCuspLift.vector,
    inv_smul_smul₀ (FrameProfile.character_ne_zero _ _), realFrame_point frame fullRank]

theorem tuple {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re)
    (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ProfileTuples.tuple (RecoveryGlobalCusp.section_induced induced halfPlane) frame =
      TupleRecoveryOperator.operator data parameter halfPlane (ProfileTuples.tuple induced frame) := by
  funext key
  change (FrameProfile.profile (RecoveryGlobalCusp.section_induced induced halfPlane)
    (RealFrameChart.adelicFrame (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key)) frame)).val = _
  rw [profile induced halfPlane (UniversalFiniteProfiles.representative data key) frame fullRank,
    SmoothTupleOperator.averagedRow_val]
  rfl

def generators {degree : ℕ} (data : InducingData degree) (parameter : ℂ) : Set (ProfileTuples.Space data) :=
  {value | ∃ function : AdelicGL → ℂ, ∃ induced : IsInduced data .plane parameter function,
    ∃ frame : Rectangular ℝ, FullRank frame ∧ ProfileTuples.tuple induced frame = value}

def admissible {degree : ℕ} (data : InducingData degree) (parameter : ℂ) : Submodule ℂ (ProfileTuples.Space data) :=
  (Submodule.span ℂ (generators data parameter)).topologicalClosure

theorem tuple_mem {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) (fullRank : FullRank frame) :
    ProfileTuples.tuple induced frame ∈ admissible data parameter :=
  (Submodule.span ℂ (generators data parameter)).le_topologicalClosure
    (Submodule.subset_span ⟨function, induced, frame, fullRank, rfl⟩)

theorem admissible_le {degree : ℕ} (data : InducingData degree) (parameter : ℂ) :
    admissible data parameter ≤ ProfileTuples.admissible data := by
  apply (Submodule.span ℂ (generators data parameter)).topologicalClosure_minimal _ (ProfileTuples.admissible_isClosed data)
  apply Submodule.span_le.mpr
  rintro _ ⟨function, induced, frame, fullRank, rfl⟩
  exact ProfileTuples.tuple_admissible induced frame fullRank

theorem admissible_closed {degree : ℕ} (data : InducingData degree) (parameter : ℂ) :
    IsClosed (admissible data parameter : Set (ProfileTuples.Space data)) :=
  (Submodule.span ℂ (generators data parameter)).isClosed_topologicalClosure

theorem operator_preserves {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ parameter.re) (value : ProfileTuples.Space data)
    (membership : value ∈ admissible data parameter) :
    TupleRecoveryOperator.operator data parameter halfPlane value ∈ admissible data parameter := by
  let inverseImage : Submodule ℂ (ProfileTuples.Space data) :=
    (admissible data parameter).comap (TupleRecoveryOperator.operator data parameter halfPlane).toLinearMap
  have closed : IsClosed (inverseImage : Set (ProfileTuples.Space data)) :=
    (admissible_closed data parameter).preimage (TupleRecoveryOperator.operator data parameter halfPlane).continuous
  have contained : admissible data parameter ≤ inverseImage := by
    apply (Submodule.span ℂ (generators data parameter)).topologicalClosure_minimal _ closed
    apply Submodule.span_le.mpr
    rintro _ ⟨function, induced, frame, fullRank, rfl⟩
    change TupleRecoveryOperator.operator data parameter halfPlane (ProfileTuples.tuple induced frame) ∈ admissible data parameter
    rw [← tuple induced halfPlane frame fullRank]
    exact tuple_mem (RecoveryGlobalCusp.section_induced induced halfPlane) frame fullRank
  exact contained membership

theorem primitive_identity {degree : ℕ} (data : InducingData degree) (parameter reference : ℂ)
    (halfPlane : -(degree : ℝ) / 2 ≤ reference.re) (value : ProfileTuples.Space data)
    (membership : value ∈ admissible data parameter) :
    TupleRecoveryOperator.primitiveOperator data reference halfPlane value = (FinitePrimitiveRecovery.mass : ℂ) • value :=
  PrimitiveTupleIdentity.admissible_identity data reference halfPlane value (admissible_le data parameter membership)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.TupleInducedRecovery
