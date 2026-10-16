module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.BoxSymmetry

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegralFrameOrbit
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileResidues TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryLevel

def subgroup {degree : ℕ} (data : InducingData degree) : OpenNormalSubgroup IntegralFiniteGL :=
  (FiniteBoxSymmetry.exists_normal data).choose

theorem subgroup_level {degree : ℕ} (data : InducingData degree) (matrix : IntegralFiniteGL)
    (membership : matrix ∈ subgroup data) : GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel :=
  (FiniteBoxSymmetry.exists_normal data).choose_spec.1 matrix membership

theorem subgroup_character {degree : ℕ} (data : InducingData degree) (matrix : IntegralFiniteGL)
    (membership : matrix ∈ subgroup data) : character data matrix = 1 :=
  (FiniteBoxSymmetry.exists_normal data).choose_spec.2.1 matrix membership

theorem subgroup_boxes {degree : ℕ} (data : InducingData degree) (matrix : IntegralFiniteGL)
    (membership : matrix ∈ subgroup data) (key : UniversalFiniteProfiles.Key data) (value : Rectangular FiniteAdeles) :
    (UniversalFiniteProfiles.boxes data key).test ((GeneralLinearGroup.map integralEmbedding matrix).val * value) =
      (UniversalFiniteProfiles.boxes data key).test value :=
  (FiniteBoxSymmetry.exists_normal data).choose_spec.2.2 matrix membership key value

theorem finite_frame_right (point : AdelicGL) (matrix : FiniteGL) (binary : BinaryFiniteGL) :
    finite (FrameProfile.frame (point * atFinite matrix) * (atFinite binary).val) =
      matrix⁻¹.val * finite (FrameProfile.frame point * (atFinite binary).val) := by
  unfold FrameProfile.frame finite
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rfl

theorem realFrame_right (point : AdelicGL) (matrix : FiniteGL) :
    realFrame (point * atFinite matrix) = realFrame point := by
  have realIdentity : realGroup (atFinite matrix) = 1 := by apply Units.ext; rfl
  rw [realFrame, map_mul, realIdentity, mul_one]
  rfl

theorem coefficient_right {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (point : AdelicGL)
    (matrix : IntegralFiniteGL) (membership : matrix ∈ subgroup data)
    (key : UniversalFiniteProfiles.Key data) (binary : BinaryFiniteGL) :
    RecoveryCoefficients.coefficient data parameter
      (point * atFinite (GeneralLinearGroup.map integralEmbedding matrix)) key binary =
        RecoveryCoefficients.coefficient data parameter point key binary := by
  rw [RecoveryCoefficients.coefficient, finite_frame_right]
  rw [← map_inv, subgroup_boxes data matrix⁻¹ ((subgroup data).toOpenSubgroup.inv_mem membership)]
  rfl

theorem outer_integral {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (matrix : IntegralFiniteGL) :
    outerCharacter data parameter (GeneralLinearGroup.det (atFinite (GeneralLinearGroup.map integralEmbedding matrix))) =
      character data matrix := by
  change data.chi.toMonoidHom _ * normPower _ _ = _
  rw [normPower, Norm.adeleNorm_det_integral]
  simp only [NNReal.coe_one, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rfl

theorem kernel_right {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL)
    (matrix : IntegralFiniteGL) (membership : matrix ∈ subgroup data) (binary : BinaryFiniteGL) :
    RealBinaryRecovery.kernel induced (point * atFinite (GeneralLinearGroup.map integralEmbedding matrix)) (atFinite binary) =
      RealBinaryRecovery.kernel induced point (atFinite binary) := by
  simp only [RecoveryCoefficients.kernel_eq, coefficient_right data parameter point matrix membership, realFrame_right]

theorem section_right {degree : ℕ} {data : InducingData degree} {parameter : ℂ} {function : AdelicGL → ℂ}
    (induced : IsInduced data .plane parameter function) (point : AdelicGL)
    (matrix : IntegralFiniteGL) (membership : matrix ∈ subgroup data) :
    FiniteRecoveryIntegral.sectionFunction induced (point * atFinite (GeneralLinearGroup.map integralEmbedding matrix)) =
      FiniteRecoveryIntegral.sectionFunction induced point := by
  simp only [FiniteRecoveryIntegral.sectionFunction, map_mul, outer_integral,
    subgroup_character data matrix membership, mul_one, kernel_right induced point matrix membership]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RecoveryLevel
