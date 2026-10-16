module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LinearProfileRecovery

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFrameChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealBinaryRecovery

theorem real_mul_infinity (value : Rectangular Adeles) (binary : BinaryRealGL) :
    coordinateEquiv.symm (archimedean (value * (atInfinity binary).val)) =
      coordinateEquiv.symm (archimedean value) * binary.val := by
  change (value * (atInfinity binary).val).map (RingHom.fst ℝ FiniteAdeles) =
    value.map (RingHom.fst ℝ FiniteAdeles) * binary.val
  rw [Matrix.map_mul]
  rfl

theorem finite_mul_infinity (value : Rectangular Adeles) (binary : BinaryRealGL) :
    finite (value * (atInfinity binary).val) = finite value := by
  change (value * (atInfinity binary).val).map (RingHom.snd ℝ FiniteAdeles) = _
  rw [Matrix.map_mul]
  change finite value * 1 = finite value
  exact Matrix.mul_one _

theorem real_mul_finite (value : Rectangular Adeles) (binary : BinaryFiniteGL) :
    coordinateEquiv.symm (archimedean (value * (atFinite binary).val)) =
      coordinateEquiv.symm (archimedean value) := by
  change (value * (atFinite binary).val).map (RingHom.fst ℝ FiniteAdeles) = _
  rw [Matrix.map_mul]
  change value.map (RingHom.fst ℝ FiniteAdeles) * 1 = _
  exact Matrix.mul_one _

theorem adelicFrame_mul_infinity (point : FiniteGL) (value : Rectangular ℝ) (binary : BinaryRealGL) :
    adelicFrame point (value * binary.val) = adelicFrame point value * (atInfinity binary).val := by
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · exact (congrArg (fun matrix : Rectangular ℝ => matrix row column)
      (real_mul_infinity (adelicFrame point value) binary)).symm
  · exact (congrArg (fun matrix : Rectangular FiniteAdeles => matrix row column)
      (finite_mul_infinity (adelicFrame point value) binary)).symm

theorem realize_profile_infinity {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : FiniteGL) (value : Rectangular ℝ) (fullRank : FullRank value)
    (binary : BinaryRealGL) (evaluation : BinaryAdelicGL) :
    data.cusp.realize (profile induced (adelicFrame point (value * binary.val)))
      (evaluation * atInfinity binary) =
        (innerCharacter data parameter (GeneralLinearGroup.det (atInfinity binary)))⁻¹ *
          data.cusp.realize (profile induced (adelicFrame point value)) evaluation := by
  rw [adelicFrame_mul_infinity, RealFrameChart.adelicFrame_eq point value fullRank,
    realize_profile_frame_mul, mul_inv_cancel_right, profile_frame]

theorem real_orbit_fullRank (point : AdelicGL) (binary : BinaryAdelicGL) :
    FullRank (coordinateEquiv.symm (archimedean (FrameProfile.frame point * binary.val))) := by
  rw [← FrameProfile.frame_levi, ← realFrame_eq]
  exact realFrame_fullRank _

def kernel {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  ∑ key : UniversalFiniteProfiles.Key data,
    (UniversalFiniteProfiles.boxes data key).test (finite (FrameProfile.frame point * binary.val)) *
      (innerCharacter data parameter (GeneralLinearGroup.det binary) *
        data.cusp.realize (profile induced
          (adelicFrame (GeneralLinearGroup.map integralEmbedding (UniversalFiniteProfiles.representative data key))
            (coordinateEquiv.symm (archimedean (FrameProfile.frame point * binary.val))))) binary)

theorem integrand_eq_kernel {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular ℝ → ℝ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    VectorGodement.integrand data (LinearProfileRecovery.test induced cutoff) parameter point binary =
      (cutoff (coordinateEquiv.symm (archimedean (FrameProfile.frame point * binary.val))) : ℂ) *
        kernel induced point binary := by
  simp only [VectorGodement.integrand, LinearProfileRecovery.test, kernel, map_sum, Finset.sum_apply,
    map_smul, LinearMap.map_smul_of_tower, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro key _
  ring

theorem kernel_infinity {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (point : AdelicGL) (binary : BinaryAdelicGL) (realBinary : BinaryRealGL) :
    kernel induced point (binary * atInfinity realBinary) = kernel induced point binary := by
  simp only [kernel, Units.val_mul, ← Matrix.mul_assoc, finite_mul_infinity,
    real_mul_infinity, map_mul, realize_profile_infinity induced _ _ (real_orbit_fullRank point binary)]
  apply Finset.sum_congr rfl
  intro key _
  have nonzero := FrameProfile.character_ne_zero (innerCharacter data parameter)
    (GeneralLinearGroup.det (atInfinity realBinary))
  field_simp

theorem integrand_separated {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {function : AdelicGL → ℂ} (induced : IsInduced data .plane parameter function)
    (cutoff : Rectangular ℝ → ℝ) (point : AdelicGL)
    (finiteBinary : BinaryFiniteGL) (realBinary : BinaryRealGL) :
    VectorGodement.integrand data (LinearProfileRecovery.test induced cutoff) parameter point
      (atFinite finiteBinary * atInfinity realBinary) =
        (cutoff (realFrame point * realBinary.val) : ℂ) * kernel induced point (atFinite finiteBinary) := by
  rw [integrand_eq_kernel, kernel_infinity, Units.val_mul, ← Matrix.mul_assoc,
    real_mul_infinity, real_mul_finite, ← realFrame_eq]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealBinaryRecovery
