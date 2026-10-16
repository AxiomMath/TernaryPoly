module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProfileTuples

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveTupleKernel

def kernel {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : AdelicGL)
    (tuple : ProfileTuples.Space data) (binary : BinaryFiniteGL) : data.cusp.H :=
  ∑ key : UniversalFiniteProfiles.Key data, RecoveryCoefficients.coefficient data parameter point key binary •
    data.cusp.π (atFinite binary) (tuple key)

theorem profile_translate_cancel {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (binary : BinaryAdelicGL) :
    innerCharacter data parameter (GeneralLinearGroup.det binary) •
      data.cusp.π binary (profile induced (frame point * binary.val)).val = (normalized induced point).val := by
  let translated : data.cusp.smooth :=
    ⟨data.cusp.π binary (profile induced (frame point * binary.val)).val,
      data.cusp.smooth_stable _ _ (profile induced (frame point * binary.val)).property⟩
  change (innerCharacter data parameter (GeneralLinearGroup.det binary) • translated : data.cusp.smooth).val = _
  apply congrArg Subtype.val
  apply data.cusp.injective
  funext evaluation
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [show data.cusp.realize translated evaluation =
    data.cusp.realize (profile induced (frame point * binary.val)) (evaluation * binary) from data.cusp.equivariant _ _ _,
    realize_profile_frame_mul, mul_inv_cancel_right, mul_inv_cancel_left₀ (character_ne_zero _ _)]

theorem primitive_profiles {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryFiniteGL) (primitive : binary ∈ FinitePrimitiveRecovery.integralGroup) :
    (∑ key : UniversalFiniteProfiles.Key data,
      (UniversalFiniteProfiles.boxes data key).test (finite (frame point * (atFinite binary).val)) •
        ProfileTuples.vectors induced (realFrame point) key) = profile induced (frame point * (atFinite binary).val) := by
  obtain ⟨finitePoint, orbitEquality⟩ := orbit_integral point pointIntegral (atFinite binary) primitive
  have equality := LinearProfileRecovery.test_primitive induced (fun _ => 1) finitePoint
    (realFrame (planeLevi (atFinite binary)⁻¹ 1 * point)) (realFrame_fullRank _)
  rw [← orbitEquality] at equality
  simpa only [LinearProfileRecovery.test, ProfileTuples.vectors, one_smul,
    RealBinaryRecovery.real_mul_finite, ← realFrame_eq] using equality

theorem kernel_primitive {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : BinaryFiniteGL) (primitive : binary ∈ FinitePrimitiveRecovery.integralGroup) :
    kernel data parameter point (ProfileTuples.tuple induced (realFrame point)) binary =
      (normalized induced point).val := by
  have equality := congrArg (fun vector : data.cusp.smooth =>
    innerCharacter data parameter (GeneralLinearGroup.det (atFinite binary)) • data.cusp.π (atFinite binary) vector.val)
    (primitive_profiles induced point pointIntegral binary primitive)
  have leftEquality : kernel data parameter point (ProfileTuples.tuple induced (realFrame point)) binary =
      innerCharacter data parameter (GeneralLinearGroup.det (atFinite binary)) • data.cusp.π (atFinite binary)
        (∑ key : UniversalFiniteProfiles.Key data,
          (UniversalFiniteProfiles.boxes data key).test (finite (frame point * (atFinite binary).val)) •
            ProfileTuples.vectors induced (realFrame point) key).val := by
    simp only [kernel, RecoveryCoefficients.coefficient, ProfileTuples.tuple, Submodule.coe_sum,
      Submodule.coe_smul, map_sum, map_smul, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro key _
    rw [mul_comm]
  exact leftEquality.trans (equality.trans (profile_translate_cancel induced point (atFinite binary)))

theorem finite_frame_infinity (point : AdelicGL) (realPoint : RealGL3) :
    finite (frame (point * atInfinity realPoint)) = finite (frame point) := by
  unfold frame finite
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.map_mul]
  have identity : (atInfinity realPoint)⁻¹.val.map (RingHom.snd ℝ FiniteAdeles) = 1 := rfl
  rw [identity, Matrix.one_mul]

theorem coefficient_infinity {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (point : AdelicGL) (realPoint : RealGL3) (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL) :
    RecoveryCoefficients.coefficient data parameter (point * atInfinity realPoint) key binary =
      RecoveryCoefficients.coefficient data parameter point key binary := by
  simp only [RecoveryCoefficients.coefficient, RecoveryCoefficients.finite_orbit, finite_frame_infinity]

theorem realFrame_chart (finitePoint : FiniteGL) (value : Rectangular ℝ) (fullRank : FullRank value) :
    realFrame (atFinite finitePoint * atInfinity (RealFrameChart.point value)) = value := by
  rw [realFrame_eq, ← adelicFrame_eq finitePoint value fullRank]
  rfl

theorem kernel_chart {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (finitePoint : IntegralFiniteGL) (value : Rectangular ℝ) (fullRank : FullRank value)
    (binary : BinaryFiniteGL) (primitive : binary ∈ FinitePrimitiveRecovery.integralGroup) :
    kernel data parameter (atFinite (GeneralLinearGroup.map integralEmbedding finitePoint))
      (ProfileTuples.tuple induced value) binary =
        (profile induced (adelicFrame (GeneralLinearGroup.map integralEmbedding finitePoint) value)).val := by
  let point := atFinite (GeneralLinearGroup.map integralEmbedding finitePoint) * atInfinity (RealFrameChart.point value)
  have pointIntegral : finiteGroup point ∈ Set.range (GeneralLinearGroup.map integralEmbedding) := by
    refine ⟨finitePoint, ?_⟩
    change GeneralLinearGroup.map integralEmbedding finitePoint = finiteGroup
      (atFinite (GeneralLinearGroup.map integralEmbedding finitePoint) * atInfinity (RealFrameChart.point value))
    rw [map_mul]
    change _ = _ * 1
    rw [mul_one]
    rfl
  have equality := kernel_primitive induced point pointIntegral binary primitive
  simpa only [point, realFrame_chart _ value fullRank, kernel, coefficient_infinity,
    ← RealFrameChart.profile_eq induced _ value fullRank] using equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PrimitiveTupleKernel
