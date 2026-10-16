module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.Integral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularKernel TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile

def frame (point : AdelicGL) : Rectangular Adeles := point⁻¹.val * standard

theorem frame_levi (point : AdelicGL) (binary : BinaryAdelicGL) :
    frame (planeLevi binary⁻¹ 1 * point) = frame point * binary.val := by
  have identity := FrameFlags.standard_right binary
  change columns (planeLevi binary 1).val = standard * binary.val at identity
  have inverse : (planeLevi binary⁻¹ (1 : Adelesˣ))⁻¹ = planeLevi binary 1 := by
    apply Units.ext
    simp [planeLevi, planeBlock]
  unfold frame
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, inverse]
  rw [show (planeLevi binary 1).val * standard = columns (planeLevi binary 1).val from
    mul_standard _, identity, Matrix.mul_assoc]

theorem standard_stabilizer (matrix : AdelicGL)
    (fixed : matrix.val * standard = standard) :
    ∃ first second : Adeles, ∃ scalar : Adelesˣ,
      matrix = planeUnipotent first second * planeLevi 1 scalar := by
  have columnsFixed : columns matrix.val = standard := by
    simpa only [standard, mul_standard] using fixed
  have entry (row : Fin 3) (column : Fin 2) :
      matrix.val row column.castSucc = (standard : Rectangular Adeles) row column :=
    congrArg (fun value : Rectangular Adeles => value row column) columnsFixed
  have membership : matrix ∈ planeParabolic Adeles := by
    constructor
    · simpa [standard, columns, Matrix.one_apply] using entry 2 0
    · simpa [standard, columns, Matrix.one_apply] using entry 2 1
  let parabolic : planeParabolic Adeles := ⟨matrix, membership⟩
  have block : planeBinaryBlock parabolic = 1 := by
    apply Units.ext
    apply Matrix.ext
    intro row column
    change matrix.val row.castSucc column.castSucc = (1 : Matrix (Fin 2) (Fin 2) Adeles) row column
    simpa [standard, columns, Matrix.one_apply] using entry row.castSucc column
  refine ⟨matrix.val 0 2 * (planeCornerUnit parabolic).inv,
    matrix.val 1 2 * (planeCornerUnit parabolic).inv, planeCornerUnit parabolic, ?_⟩
  simpa only [block] using planeParabolic_factorization parabolic

def normalized {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : AdelicGL → ℂ} (induced : IsInduced data .plane parameter sectionFunction)
    (point : AdelicGL) : data.cusp.smooth :=
  (outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ • planeCuspVector induced point

theorem character_ne_zero (character : Adelesˣ →* ℂ) (scalar : Adelesˣ) : character scalar ≠ 0 := by
  intro vanishing
  have equality := map_mul character scalar scalar⁻¹
  simp only [mul_inv_cancel, map_one, vanishing, zero_mul, one_ne_zero] at equality

theorem normalized_stabilizer {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : AdelicGL → ℂ} (induced : IsInduced data .plane parameter sectionFunction)
    (point : AdelicGL) (first second : Adeles) (scalar : Adelesˣ) :
    normalized induced (planeUnipotent first second * (planeLevi 1 scalar * point)) =
      normalized induced point := by
  have nonzero : outerCharacter data parameter scalar ≠ 0 :=
    character_ne_zero _ _
  unfold normalized
  rw [planeCuspVector_unipotent, planeCuspVector_scalar, map_mul, det_planeUnipotent,
    one_mul, map_mul, det_planeLevi, map_one, one_mul, map_mul, smul_smul]
  change ((outerCharacter data parameter scalar * outerCharacter data parameter (GeneralLinearGroup.det point))⁻¹ *
    outerCharacter data parameter scalar) • _ = _
  rw [mul_inv, mul_right_comm, inv_mul_cancel₀ nonzero, one_mul]

theorem normalized_eq_of_frame_eq {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : AdelicGL → ℂ} (induced : IsInduced data .plane parameter sectionFunction)
    (first second : AdelicGL) (equality : frame first = frame second) :
    normalized induced first = normalized induced second := by
  have fixed : (first * second⁻¹).val * standard = standard := by
    rw [Units.val_mul, Matrix.mul_assoc, ← show frame second = second⁻¹.val * standard from rfl,
      ← equality]
    unfold frame
    have inverse : first.val * first⁻¹.val = 1 := first.val_inv
    rw [← Matrix.mul_assoc, inverse, Matrix.one_mul]
  obtain ⟨a, b, scalar, factorization⟩ := standard_stabilizer (first * second⁻¹) fixed
  have firstEquality : first = planeUnipotent a b * (planeLevi 1 scalar * second) := by
    rw [← mul_assoc, ← factorization, inv_mul_cancel_right]
  rw [firstEquality, normalized_stabilizer]

def profile {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : AdelicGL → ℂ} (induced : IsInduced data .plane parameter sectionFunction)
    (value : Rectangular Adeles) : data.cusp.smooth :=
  if existsPoint : ∃ point, frame point = value then normalized induced existsPoint.choose else 0

theorem profile_frame {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : AdelicGL → ℂ} (induced : IsInduced data .plane parameter sectionFunction)
    (point : AdelicGL) : profile induced (frame point) = normalized induced point := by
  have existsPoint : ∃ other, frame other = frame point := ⟨point, rfl⟩
  rw [profile, dite_eq_left existsPoint]
  exact normalized_eq_of_frame_eq induced _ _ existsPoint.choose_spec

theorem realize_profile_frame_mul {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionFunction : AdelicGL → ℂ} (induced : IsInduced data .plane parameter sectionFunction)
    (point : AdelicGL) (binary evaluation : BinaryAdelicGL) :
    data.cusp.realize (profile induced (frame point * binary.val)) evaluation =
      (innerCharacter data parameter (GeneralLinearGroup.det binary))⁻¹ *
        data.cusp.realize (normalized induced point) (evaluation * binary⁻¹) := by
  rw [← frame_levi, profile_frame]
  unfold normalized
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, planeCuspVector_binaryLevi,
    data.cusp.equivariant, map_mul, det_planeLevi, mul_one, map_inv]
  have product := characters_product data parameter (GeneralLinearGroup.det binary)
  have outerNonzero : outerCharacter data parameter (GeneralLinearGroup.det binary) ≠ 0 :=
    character_ne_zero _ _
  have innerNonzero : innerCharacter data parameter (GeneralLinearGroup.det binary) ≠ 0 :=
    character_ne_zero _ _
  have powerInverse : normPower (GeneralLinearGroup.det binary)⁻¹
      (binaryInductionExponent degree .plane parameter) =
      (normPower (GeneralLinearGroup.det binary) (binaryInductionExponent degree .plane parameter))⁻¹ := by
    have equality := normPower_mul (GeneralLinearGroup.det binary)
      (GeneralLinearGroup.det binary)⁻¹ (binaryInductionExponent degree .plane parameter)
    rw [mul_inv_cancel, normPower_one] at equality
    exact (inv_eq_of_mul_eq_one_right equality.symm).symm
  rw [powerInverse, ← product, mul_inv, inv_inv, mul_inv]
  field_simp

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameProfile
