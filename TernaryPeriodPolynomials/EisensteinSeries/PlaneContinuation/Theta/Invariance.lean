module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.Integral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameFlags TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaInvariance

def leftTranslate (matrix : RationalGL3) (frame : Frame) : Frame :=
  ⟨matrix.val * frame.val, by
    rw [← complete_columns frame, ← columns_mul]
    exact columns_fullRank (matrix * complete frame)⟩

theorem leftTranslate_mul (first second : RationalGL3) (frame : Frame) :
    leftTranslate (first * second) frame = leftTranslate first (leftTranslate second frame) := by
  apply Subtype.ext
  exact Matrix.mul_assoc _ _ _

theorem leftTranslate_one (frame : Frame) : leftTranslate 1 frame = frame := by
  apply Subtype.ext
  exact Matrix.one_mul _

def leftEquiv (matrix : RationalGL3) : Frame ≃ Frame where
  toFun := leftTranslate matrix
  invFun := leftTranslate matrix⁻¹
  left_inv frame := by rw [← leftTranslate_mul, inv_mul_cancel, leftTranslate_one]
  right_inv frame := by rw [← leftTranslate_mul, mul_inv_cancel, leftTranslate_one]

def rightEquiv (matrix : BinaryRationalGL) : Frame ≃ Frame where
  toFun frame := changeBasis frame matrix
  invFun frame := changeBasis frame matrix⁻¹
  left_inv frame := by
    change changeBasis (changeBasis frame matrix) matrix⁻¹ = frame
    rw [← changeBasis_mul, mul_inv_cancel, changeBasis_one]
  right_inv frame := by
    change changeBasis (changeBasis frame matrix⁻¹) matrix = frame
    rw [← changeBasis_mul, inv_mul_cancel, changeBasis_one]

theorem term_rational_left (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : RationalGL3) (frame : Frame) :
    term test (rationalGroup rational * point) binary frame =
      term test point binary (leftEquiv rational⁻¹ frame) := by
  unfold term
  change test ((rationalGroup rational * point)⁻¹.val * frame.val.map rationalAdele * binary.val) =
    test (point⁻¹.val * (rational⁻¹.val * frame.val).map rationalAdele * binary.val)
  rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, Matrix.map_mul]
  change test ((point⁻¹.val * (rationalGroup rational⁻¹).val) * frame.val.map rationalAdele * binary.val) = _
  simp only [Matrix.mul_assoc]
  rfl

theorem term_rational_binary (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) (frame : Frame) :
    term test point (GeneralLinearGroup.map rationalAdele rational * binary) frame =
      term test point binary (rightEquiv rational frame) := by
  unfold term
  change test (point⁻¹.val * frame.val.map rationalAdele *
      (GeneralLinearGroup.map rationalAdele rational * binary).val) =
    test (point⁻¹.val * (frame.val * rational.val).map rationalAdele * binary.val)
  rw [Units.val_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rfl

theorem theta_rational_left (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : RationalGL3) : theta test (rationalGroup rational * point) binary = theta test point binary := by
  simp only [theta, term_rational_left]
  exact (leftEquiv rational⁻¹).tsum_eq _

theorem theta_rational_binary (test : Rectangular Adeles → ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) :
    theta test point (GeneralLinearGroup.map rationalAdele rational * binary) = theta test point binary := by
  simp only [theta, term_rational_binary]
  exact (rightEquiv rational).tsum_eq _

theorem innerCharacter_rational {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (scalar : ℚˣ) :
    GodementIntegral.innerCharacter data parameter (Units.map rationalAdele.toMonoidHom scalar) = 1 := by
  change (data.chi.toMonoidHom (Units.map rationalAdele.toMonoidHom scalar))⁻¹ * normPower _ _ = 1
  have characterValue : data.chi.toMonoidHom (Units.map rationalAdele.toMonoidHom scalar) = 1 := data.chi.rational scalar
  have powerValue : normPower (Units.map rationalAdele.toMonoidHom scalar)
      (binaryInductionExponent degree .plane parameter + 2 * inductionExponent .plane parameter) = 1 :=
    ProductFormula.normPower_rational scalar _
  rw [characterValue, inv_one, powerValue, mul_one]

theorem outerCharacter_rational {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (scalar : ℚˣ) :
    GodementIntegral.outerCharacter data parameter (Units.map rationalAdele.toMonoidHom scalar) = 1 := by
  change data.chi.toMonoidHom (Units.map rationalAdele.toMonoidHom scalar) * normPower _ _ = 1
  have characterValue : data.chi.toMonoidHom (Units.map rationalAdele.toMonoidHom scalar) = 1 := data.chi.rational scalar
  have powerValue : normPower (Units.map rationalAdele.toMonoidHom scalar)
      (-2 * inductionExponent .plane parameter) = 1 := ProductFormula.normPower_rational scalar _
  rw [characterValue, powerValue, mul_one]

noncomputable def integrand {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  theta test point binary * GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det binary) *
    data.cusp.realize vector binary

theorem integrand_rational_binary {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (parameter : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL)
    (rational : BinaryRationalGL) :
    integrand data test vector parameter point (GeneralLinearGroup.map rationalAdele rational * binary) =
      integrand data test vector parameter point binary := by
  have rationalValue : GodementIntegral.innerCharacter data parameter
      (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact innerCharacter_rational data parameter (GeneralLinearGroup.det rational)
  unfold integrand
  rw [theta_rational_binary, map_mul, map_mul, rationalValue, one_mul, data.cusp.leftRational]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaInvariance
