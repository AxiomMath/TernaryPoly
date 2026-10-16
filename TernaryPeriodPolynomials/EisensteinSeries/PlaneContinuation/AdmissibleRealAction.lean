module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Tuple.ParameterShift
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProfileTuples TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open scoped Classical Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdmissibleRealAction

def action {degree : ℕ} (data : InducingData degree) (matrix : BinaryRealGL) : Space data →L[ℂ] Space data :=
  ContinuousLinearMap.pi (fun key => (FiniteHilbertConvolution.action data.cusp (atInfinity matrix)).comp
    (ContinuousLinearMap.proj key))

theorem action_apply {degree : ℕ} (data : InducingData degree) (matrix : BinaryRealGL)
    (value : Space data) (key : UniversalFiniteProfiles.Key data) :
    action data matrix value key = data.cusp.π (atInfinity matrix) (value key) := rfl

theorem tuple_levi {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (realPoint : RealGL3) (matrix : BinaryRealGL) :
    tuple induced (realFrame (atInfinity (planeLevi matrix 1 * realPoint))) =
      GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det (atInfinity matrix)) •
        action data matrix (tuple induced (realFrame (atInfinity realPoint))) :=
  congrArg (fun value : SmoothTupleOperator.Space data => fun key => (value key).val)
    (TupleRealCovariance.vectors_levi induced realPoint matrix)

theorem action_tuple_mem {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (frame : Rectangular ℝ) (fullRank : FullRank frame)
    (matrix : BinaryRealGL) : action data matrix (tuple induced frame) ∈ admissible data := by
  have membership := (admissible data).smul_mem
    (GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det (atInfinity matrix)))⁻¹
    (tuple_admissible induced (realFrame (atInfinity (planeLevi matrix 1 * RealFrameChart.point frame))) (realFrame_fullRank _))
  rw [tuple_levi, inv_smul_smul₀ (FrameProfile.character_ne_zero _ _), TupleInducedRecovery.realFrame_point frame fullRank] at membership
  exact membership

theorem action_mem {degree : ℕ} (data : InducingData degree) (matrix : BinaryRealGL)
    (value : Space data) (membership : value ∈ admissible data) : action data matrix value ∈ admissible data := by
  let inverseImage : Submodule ℂ (Space data) := (admissible data).comap (action data matrix).toLinearMap
  have closed : IsClosed (inverseImage : Set (Space data)) :=
    (admissible_isClosed data).preimage (action data matrix).continuous
  have contained : admissible data ≤ inverseImage := by
    apply (Submodule.span ℂ (generators data)).topologicalClosure_minimal _ closed
    apply Submodule.span_le.mpr
    rintro _ ⟨parameter, function, induced, frame, fullRank, rfl⟩
    exact action_tuple_mem induced frame fullRank matrix
  exact contained membership

theorem directional_mem {degree : ℕ} (data : InducingData degree) (value : SmoothTupleOperator.Space data)
    (membership : (fun key => (value key).val) ∈ admissible data) (direction : OrbitSmooth.BinaryMatrix) :
    (fun key => (AnalyticDifferentiation.directionalOperator data.cusp direction (value key)).val) ∈ admissible data := by
  let orbit : OrbitSmooth.BinaryMatrix → Space data :=
    fun matrix => action data (invertibleMatrix matrix) (fun key => (value key).val)
  let derivative : OrbitSmooth.BinaryMatrix →L[ℝ] Space data :=
    ContinuousLinearMap.pi (fun key => fderiv ℝ (OrbitTranslation.realOrbit data.cusp (value key).val) 1)
  have differentiable : HasFDerivAt orbit derivative 1 := by
    apply hasFDerivAt_pi.mpr
    intro key
    exact ((SobolevSeminorms.smooth_orbit_contDiffAt_one data.cusp (value key)).differentiableAt (by simp)).hasFDerivAt
  apply (admissible_isClosed data).mem_of_tendsto (differentiable.lim_real direction)
  apply Eventually.of_forall
  intro scalar
  exact (admissible data).smul_mem (scalar : ℂ)
    ((admissible data).sub_mem (action_mem data _ _ membership) (action_mem data _ _ membership))

theorem mode_mem {degree : ℕ} (data : InducingData degree) (index : ℤ) (value : Space data)
    (membership : value ∈ admissible data) :
    (fun key => RotationFourier.modeVector data.cusp index (value key)) ∈ admissible data := by
  let integrand : RotationCircle.Parameter → Space data :=
    fun parameter => fourier (-index) parameter • action data (RotationCircle.rotation parameter) value
  have continuous : Continuous integrand := by
    apply Continuous.smul (fourier (-index)).continuous
    exact continuous_pi (fun key => RotationFourier.orbit_continuous data.cusp (value key))
  have integrable : Integrable integrand AddCircle.haarAddCircle :=
    continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have integralMembership : (∫ parameter, integrand parameter ∂AddCircle.haarAddCircle) ∈ admissible data :=
    ((admissible data).restrictScalars ℝ).convex.integral_mem (admissible_isClosed data)
      (Eventually.of_forall (fun parameter => (admissible data).smul_mem _ (action_mem data _ value membership))) integrable
  have equality : (∫ parameter, integrand parameter ∂AddCircle.haarAddCircle) =
      fun key => RotationFourier.modeVector data.cusp index (value key) := by
    funext key
    exact ((ContinuousLinearMap.proj key : Space data →L[ℂ] data.cusp.H).integral_comp_comm integrable).symm
  exact equality ▸ integralMembership

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdmissibleRealAction
