module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import TernaryPeriodPolynomials.Polynomial.GLAction
public import TernaryPeriodPolynomials.Polynomial.Operators
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.ReferenceCoefficientMatrices

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ
abbrev IntegralGL := ModThreeGoodAction.IntegralGL
abbrev Poly := TernaryPolynomial

def aMatrix : Mat := ![![0,-1,0], ![1,-1,0], ![0,0,1]]
def aInverseMatrix : Mat := ![![-1,1,0], ![-1,0,0], ![0,0,1]]
def cMatrix : Mat := ![![0,0,1], ![1,0,0], ![0,1,0]]
def cInverseMatrix : Mat := ![![0,1,0], ![0,0,1], ![1,0,0]]
def sMatrix : Mat := ![![0,1,0], ![1,0,0], ![0,0,1]]

theorem a_mul_inverse : aMatrix * aInverseMatrix = 1 := by decide +kernel
theorem a_inverse_mul : aInverseMatrix * aMatrix = 1 := by decide +kernel
theorem c_mul_inverse : cMatrix * cInverseMatrix = 1 := by decide +kernel
theorem c_inverse_mul : cInverseMatrix * cMatrix = 1 := by decide +kernel
theorem s_mul_self : sMatrix * sMatrix = 1 := by decide +kernel

/-- The literal order-three norm matrix, with its explicitly certified inverse. -/
def a : IntegralGL := ⟨aMatrix, aInverseMatrix, a_mul_inverse, a_inverse_mul⟩
/-- The literal cyclic reference matrix. -/
def c : IntegralGL := ⟨cMatrix, cInverseMatrix, c_mul_inverse, c_inverse_mul⟩
/-- The literal coordinate transposition. -/
def s : IntegralGL := ⟨sMatrix, sMatrix, s_mul_self, s_mul_self⟩

theorem a_inv_eq_sq : a⁻¹ = a^2 := by
  apply Units.ext
  rw [pow_two, Units.val_mul]
  change aInverseMatrix = aMatrix * aMatrix
  decide +kernel

theorem c_inv_eq_sq : c⁻¹ = c^2 := by
  apply Units.ext
  rw [pow_two, Units.val_mul]
  change cInverseMatrix = cMatrix * cMatrix
  decide +kernel

theorem s_inv_eq_self : s⁻¹ = s := rfl

theorem a_cube : a^3 = 1 := by rw [pow_succ, ← a_inv_eq_sq, inv_mul_cancel]
theorem c_cube : c^3 = 1 := by rw [pow_succ, ← c_inv_eq_sq, inv_mul_cancel]
theorem s_sq : s^2 = 1 := by
  apply Units.ext
  rw [pow_two, Units.val_mul]
  exact s_mul_self

private theorem aMatrix_det : aMatrix.det = 1 := by
  rw [Matrix.det_fin_three]
  norm_num only [ aMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
private theorem cMatrix_det : cMatrix.det = 1 := by
  rw [Matrix.det_fin_three]
  norm_num only [ cMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
private theorem sMatrix_det : sMatrix.det = -1 := by
  rw [Matrix.det_fin_three]
  norm_num only [ sMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem det_a : GeneralLinearGroup.det a = 1 := Units.ext aMatrix_det
theorem det_c : GeneralLinearGroup.det c = 1 := Units.ext cMatrix_det
theorem det_s : GeneralLinearGroup.det s = -1 := Units.ext sMatrix_det

theorem a_mem_K : a ∈ ModThreeGoodAction.K := by
  change Matrix.vecMul ModThreeGoodAction.fixedRow
    (aMatrix.map (Int.castRingHom (ZMod 3))) = ModThreeGoodAction.fixedRow
  decide +kernel

theorem c_mem_K : c ∈ ModThreeGoodAction.K := by
  change Matrix.vecMul ModThreeGoodAction.fixedRow
    (cMatrix.map (Int.castRingHom (ZMod 3))) = ModThreeGoodAction.fixedRow
  decide +kernel

theorem s_mem_K : s ∈ ModThreeGoodAction.K := by
  change Matrix.vecMul ModThreeGoodAction.fixedRow
    (sMatrix.map (Int.castRingHom (ZMod 3))) = ModThreeGoodAction.fixedRow
  decide +kernel

def aK : ModThreeGoodAction.K := ⟨a, a_mem_K⟩
def cK : ModThreeGoodAction.K := ⟨c, c_mem_K⟩
def sK : ModThreeGoodAction.K := ⟨s, s_mem_K⟩

/-- The actual coefficient-extension homomorphism to rational matrices. -/
abbrev rational : IntegralGL →* PolynomialGLAction.GL3 :=
  GeneralLinearGroup.map (Int.castRingHom ℚ)

/-- The full polynomial representation restricted along integral coefficient extension. -/
def coefficientAction (e : ℤ) : Representation ℚ IntegralGL Poly :=
  (PolynomialGLAction.action e).comp rational

/-- Inverse substitution by the literal `a` matrix is the operator `A2`. -/
theorem substitute_a_inverse :
    PolynomialGLAction.substitute ((rational a)⁻¹ : PolynomialGLAction.GL3) = TernaryPoly.A2 := by
  change PolynomialGLAction.substitute (aInverseMatrix.map (Int.castRingHom ℚ)) = TernaryPoly.A2
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    norm_num only [PolynomialGLAction.substitute_X, PolynomialGLAction.linearForm, Matrix.map, Matrix.of_apply,
      Fin.sum_univ_three, TernaryPoly.A2, bind₁_X_right, aInverseMatrix,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Int.cast_neg, Int.cast_one, Int.cast_zero, map_neg, map_one, map_zero,
      zero_mul, one_mul, zero_add, add_zero] <;> ring

/-- Inverse substitution by the literal `c` matrix is the operator `C`. -/
theorem substitute_c_inverse :
    PolynomialGLAction.substitute ((rational c)⁻¹ : PolynomialGLAction.GL3) = TernaryPoly.C := by
  change PolynomialGLAction.substitute (cInverseMatrix.map (Int.castRingHom ℚ)) = TernaryPoly.C
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    norm_num only [PolynomialGLAction.substitute_X, PolynomialGLAction.linearForm, Matrix.map, Matrix.of_apply,
      Fin.sum_univ_three, TernaryPoly.C, bind₁_X_right, cInverseMatrix,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Int.cast_neg, Int.cast_one, Int.cast_zero, map_neg, map_one, map_zero,
      zero_mul, one_mul, zero_add, add_zero]

/-- Inverse substitution by the literal `s` matrix is the operator `S`. -/
theorem substitute_s_inverse :
    PolynomialGLAction.substitute ((rational s)⁻¹ : PolynomialGLAction.GL3) = TernaryPoly.S := by
  change PolynomialGLAction.substitute (sMatrix.map (Int.castRingHom ℚ)) = TernaryPoly.S
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    norm_num only [PolynomialGLAction.substitute_X, PolynomialGLAction.linearForm, Matrix.map, Matrix.of_apply,
      Fin.sum_univ_three, TernaryPoly.S, bind₁_X_right, sMatrix,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Int.cast_neg, Int.cast_one, Int.cast_zero, map_neg, map_one, map_zero,
      zero_mul, one_mul, zero_add, add_zero]

private theorem rational_det_a : ((GeneralLinearGroup.det (rational a) : ℚˣ) : ℚ) = 1 := by
  rw [GeneralLinearGroup.map_det, det_a, map_one]
  rfl

private theorem rational_det_c : ((GeneralLinearGroup.det (rational c) : ℚˣ) : ℚ) = 1 := by
  rw [GeneralLinearGroup.map_det, det_c, map_one]
  rfl

private theorem rational_det_s : ((GeneralLinearGroup.det (rational s) : ℚˣ) : ℚ) = -1 := by
  rw [GeneralLinearGroup.map_det, det_s]
  rfl

/-- Every determinant twist has the same action of the determinant-one norm matrix. -/
theorem coefficientAction_a (e : ℤ) (f : Poly) : coefficientAction e a f = A2 f := by
  change PolynomialGLAction.action e (rational a) f = A2 f
  rw [PolynomialGLAction.action_apply, substitute_a_inverse]
  change ((GeneralLinearGroup.det (rational a) : ℚˣ) : ℚ)^e • A2 f = A2 f
  rw [rational_det_a, one_zpow, one_smul]

/-- The square of the reference norm matrix acts as the first norm substitution. -/
theorem coefficientAction_a_sq (e : ℤ) (f : Poly) : coefficientAction e (a^2) f = A f := by
  rw [pow_two, map_mul, Module.End.mul_apply, coefficientAction_a, coefficientAction_a]
  rw [← A_A (A2 f), A_A2]

/-- The literal cyclic substitution agrees with inverse matrix substitution. -/
theorem coefficientAction_c (e : ℤ) (f : Poly) : coefficientAction e c f = TernaryPoly.C f := by
  change PolynomialGLAction.action e (rational c) f = TernaryPoly.C f
  rw [PolynomialGLAction.action_apply, substitute_c_inverse]
  change ((GeneralLinearGroup.det (rational c) : ℚˣ) : ℚ)^e • TernaryPoly.C f = TernaryPoly.C f
  rw [rational_det_c, one_zpow, one_smul]

/-- The transposition carries precisely the determinant character `(-1)^e`. -/
theorem coefficientAction_s (e : ℤ) (f : Poly) :
    coefficientAction e s f = (-1 : ℚ)^e • S f := by
  change PolynomialGLAction.action e (rational s) f = _
  rw [PolynomialGLAction.action_apply, substitute_s_inverse]
  change ((GeneralLinearGroup.det (rational s) : ℚˣ) : ℚ)^e • S f = (-1 : ℚ)^e • S f
  rw [rational_det_s]

@[simp] theorem coefficientAction_zero_s (f : Poly) : coefficientAction 0 s f = S f := by
  rw [coefficientAction_s, zpow_zero, one_smul]

@[simp] theorem coefficientAction_neg_one_s (f : Poly) : coefficientAction (-1) s f = -S f := by
  rw [coefficientAction_s]
  norm_num

/-- The norm equation is exactly the reference-group norm equation for every twist. -/
theorem norm_iff (e : ℤ) (f : Poly) :
    N f = 0 ↔ f + coefficientAction e a f + coefficientAction e (a^2) f = 0 := by
  rw [N_apply, coefficientAction_a, coefficientAction_a_sq]
  have he : f + A f + A2 f = f + A2 f + A f := by abel
  rw [he]

/-- Cyclic fixedness is exactly fixedness under the actual reference group element. -/
theorem cyclic_iff (e : ℤ) (f : Poly) :
    TernaryPoly.C f = f ↔ coefficientAction e c f = f := by rw [coefficientAction_c]

/-- For exponent zero the swap sign is unchanged. -/
theorem swap_zero_iff (f : Poly) (ε : ℚ) :
    coefficientAction 0 s f = ε • f ↔ S f = ε • f := by rw [coefficientAction_zero_s]

/-- For exponent minus one the determinant twist reverses the swap sign. -/
theorem swap_neg_one_iff (f : Poly) (ε : ℚ) :
    coefficientAction (-1) s f = ε • f ↔ S f = (-ε) • f := by
  rw [coefficientAction_neg_one_s, neg_eq_iff_eq_neg, neg_smul]

/-- Both relations become actual reference-matrix equations. -/
theorem periodRelations_iff_reference (e : ℤ) (f : Poly) :
    PeriodRelations f ↔ coefficientAction e c f = f ∧
      f + coefficientAction e a f + coefficientAction e (a^2) f = 0 := by
  exact and_congr (cyclic_iff e f) (norm_iff e f)

end TernaryPoly.ReferenceCoefficientMatrices
