module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.IntegralPlaneStructure
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ParabolicFiniteness

@[expose] public section


open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.BoundaryFiniteness.ParabolicDuality

noncomputable section

def inverseTranspose : IntegralGL3 →* IntegralGL3 where
  toFun matrix :=
    ⟨(matrix⁻¹).val.transpose, matrix.val.transpose, by
      rw [← Matrix.transpose_mul]
      simpa only [Matrix.transpose_one] using congrArg Matrix.transpose matrix.mul_inv,
      by
      rw [← Matrix.transpose_mul]
      simpa only [Matrix.transpose_one] using congrArg Matrix.transpose matrix.inv_mul⟩
  map_one' := by
    apply Units.ext
    exact Matrix.transpose_one
  map_mul' left right := by
    apply Units.ext
    exact Matrix.transpose_mul (right⁻¹).val (left⁻¹).val

theorem inverseTranspose_involutive (matrix : IntegralGL3) : inverseTranspose (inverseTranspose matrix) = matrix := by
  apply Units.ext
  rfl

def inverseTransposeEquiv : IntegralGL3 ≃* IntegralGL3 where
  toFun := inverseTranspose
  invFun := inverseTranspose
  left_inv := inverseTranspose_involutive
  right_inv := inverseTranspose_involutive
  map_mul' := inverseTranspose.map_mul

def duality : IntegralGL3 ≃* IntegralGL3 :=
  inverseTransposeEquiv.trans (MulAut.conj IntegralFlags.swapFirstLast)

theorem duality_involutive (matrix : IntegralGL3) : duality (duality matrix) = matrix := by
  have fixed : inverseTranspose IntegralFlags.swapFirstLast = IntegralFlags.swapFirstLast := by
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;> rfl
  have square : IntegralFlags.swapFirstLast * IntegralFlags.swapFirstLast = 1 := by
    apply Units.ext
    exact IntegralFlags.swapFirstLast.mul_inv
  change IntegralFlags.swapFirstLast * inverseTranspose
    (IntegralFlags.swapFirstLast * inverseTranspose matrix * IntegralFlags.swapFirstLast⁻¹) *
      IntegralFlags.swapFirstLast⁻¹ = matrix
  rw [map_mul, map_mul, fixed, inverseTranspose_involutive, map_inv, fixed]
  have inverse : IntegralFlags.swapFirstLast⁻¹ = IntegralFlags.swapFirstLast := by
    apply Units.ext
    rfl
  rw [inverse]
  calc
    _ = (IntegralFlags.swapFirstLast * IntegralFlags.swapFirstLast) * matrix *
      (IntegralFlags.swapFirstLast * IntegralFlags.swapFirstLast) := by simp only [mul_assoc]
    _ = matrix := by rw [square, one_mul, mul_one]

theorem line_entries (matrix : ArithmeticStabilizers.integralParabolic .line) :
    matrix.val.val 1 0 = 0 ∧ matrix.val.val 2 0 = 0 := by
  have membership : ((matrix.val.val 1 0 : ℤ) : ℚ) = 0 ∧ ((matrix.val.val 2 0 : ℤ) : ℚ) = 0 := matrix.property
  exact ⟨Int.cast_eq_zero.mp membership.1, Int.cast_eq_zero.mp membership.2⟩

theorem duality_plane_mem (matrix : ArithmeticStabilizers.integralParabolic .plane) :
    duality matrix.val ∈ ArithmeticStabilizers.integralParabolic .line := by
  have entries := IntegralPlaneStructure.plane_entries matrix⁻¹
  change (((duality matrix.val).val 1 0 : ℤ) : ℚ) = 0 ∧
    (((duality matrix.val).val 2 0 : ℤ) : ℚ) = 0
  have first : (duality matrix.val).val 1 0 = 0 := by
    simpa [duality, inverseTransposeEquiv, inverseTranspose, IntegralFlags.swapFirstLast,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entries.2
  have second : (duality matrix.val).val 2 0 = 0 := by
    simpa [duality, inverseTransposeEquiv, inverseTranspose, IntegralFlags.swapFirstLast,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entries.1
  exact ⟨by rw [first]; rfl, by rw [second]; rfl⟩

theorem duality_line_mem (matrix : ArithmeticStabilizers.integralParabolic .line) :
    duality matrix.val ∈ ArithmeticStabilizers.integralParabolic .plane := by
  have entries := line_entries matrix⁻¹
  change (((duality matrix.val).val 2 0 : ℤ) : ℚ) = 0 ∧
    (((duality matrix.val).val 2 1 : ℤ) : ℚ) = 0
  have first : (duality matrix.val).val 2 0 = 0 := by
    simpa [duality, inverseTransposeEquiv, inverseTranspose, IntegralFlags.swapFirstLast,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entries.2
  have second : (duality matrix.val).val 2 1 = 0 := by
    simpa [duality, inverseTransposeEquiv, inverseTranspose, IntegralFlags.swapFirstLast,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entries.1
  exact ⟨by rw [first]; rfl, by rw [second]; rfl⟩

def parabolicEquiv : ArithmeticStabilizers.integralParabolic .plane ≃*
    ArithmeticStabilizers.integralParabolic .line where
  toFun matrix := ⟨duality matrix.val, duality_plane_mem matrix⟩
  invFun matrix := ⟨duality matrix.val, duality_line_mem matrix⟩
  left_inv matrix := Subtype.ext (duality_involutive matrix.val)
  right_inv matrix := Subtype.ext (duality_involutive matrix.val)
  map_mul' left right := Subtype.ext (duality.map_mul left.val right.val)

theorem parabolic_finitelyPresented (side : Side)
    [Group.IsFinitelyPresented (GeneralLinearGroup (Fin 2) ℤ)] :
    Group.IsFinitelyPresented (ArithmeticStabilizers.integralParabolic side) := by
  let := IntegralPlaneStructure.plane_finitelyPresented
  cases side
  · infer_instance
  · exact Group.IsFinitelyPresented.equiv parabolicEquiv

theorem boundary_finiteDimensional (degree : ℕ) (character : RankOneCharacter)
    [Group.IsFinitelyPresented (GeneralLinearGroup (Fin 2) ℤ)] :
    FiniteDimensional ℂ (BoundaryCoordinates degree character) := by
  let (side : Side) := parabolic_finitelyPresented side
  exact ParabolicFiniteness.boundary_finiteDimensional degree character

end

end TernaryPeriodPolynomials.BoundaryFiniteness.ParabolicDuality
