module

public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Algebra
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantLevi

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.SymmetricLineCohomology
open RadicalCoinvariantAlgebra RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The literal rational lower block of an integral Levi matrix. -/
def rationalBlock (L : GL2) : GeneralLinearGroup (Fin 2) ℚ :=
  GeneralLinearGroup.map (Int.castRingHom ℚ) L

/-- Block substitution preserves the literal last-two-coordinate polynomial embedding. -/
theorem lineLevi_substitute_rename (t : ℤˣ) (L : GL2) (J : BP) :
    PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 L)).val
      (rename Fin.succ J) =
    rename Fin.succ (binaryMatrixSubst (rationalBlock L).val J) := by
  have h : (PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 L)).val).comp
        (rename (Fin.succ : Fin 2 → Fin 3)) =
      (rename (Fin.succ : Fin 2 → Fin 3)).comp (binaryMatrixSubst (rationalBlock L).val) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [PolynomialGLAction.substitute,PolynomialGLAction.linearForm,
        GeneralLinearGroup.map_apply,Matrix.map,lineMatrix,binaryMatrixSubst,
        rationalBlock,Fin.sum_univ_three,Fin.sum_univ_two]
  exact DFunLike.congr_fun h J

/-- The full determinant character of the actual line Levi block. -/
theorem lineLevi_character (t : ℤˣ) (L : GL2) :
    PolynomialGLAction.determinantCharacter (-1)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 L)) =
      ((t.val : ℚ) * (L.val.det : ℚ))⁻¹ := by
  have hd : (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 L)).val.det =
      (t.val : ℚ) * (L.val.det : ℚ) := by
    change ((lineElement t 0 L).val.map (Int.castRingHom ℚ)).det = _
    calc
      _ = ((lineElement t 0 L).val.det : ℚ) := ((Int.castRingHom ℚ).map_det _).symm
      _ = _ := by rw [lineElement_val,det_lineMatrix]; push_cast; rfl
  change ((GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 L)).val.det)^(-1 : ℤ) = _
  rw [hd]
  simp


/-- On X-independent coefficients the genuine inverse action is binary inverse substitution,
with its full determinant-minus-one character retained. -/
theorem lineLevi_action_rename (n : ℕ) (t : ℤˣ) (L : GL2) (v : H n) (J : BP)
    (hv : (v : Poly) = rename Fin.succ J) :
    (PolynomialGLAction.integralAction n (-1) (lineElement t 0 L) v : Poly) =
      ((t.val : ℚ) * (L.val.det : ℚ))⁻¹ •
        rename Fin.succ (binaryMatrixSubst (rationalBlock L⁻¹).val J) := by
  rw [PolynomialGLAction.integralAction_coe,PolynomialGLAction.action_apply,
    lineLevi_character,hv,← map_inv,lineLevi_inv,lineLevi_substitute_rename]

/-- The determinant contraction transforms by the inverse binary matrix.
This is a polynomial identity for arbitrary rational invertible blocks. -/
theorem binary_inverse_contraction (L : GeneralLinearGroup (Fin 2) ℚ) (a b : BP) :
    MvPolynomial.C (L.val.det⁻¹) *
      (X 1 * (MvPolynomial.C (L.val 0 0) * binaryMatrixSubst (L⁻¹).val a +
              MvPolynomial.C (L.val 0 1) * binaryMatrixSubst (L⁻¹).val b) -
       X 0 * (MvPolynomial.C (L.val 1 0) * binaryMatrixSubst (L⁻¹).val a +
              MvPolynomial.C (L.val 1 1) * binaryMatrixSubst (L⁻¹).val b)) =
      binaryMatrixSubst (L⁻¹).val (X 1*a-X 0*b) := by
  rw [map_sub,map_mul,map_mul]
  have hx (i : Fin 2) : binaryMatrixSubst (L⁻¹).val (X i) =
      MvPolynomial.C (L.val.det⁻¹) *
        (MvPolynomial.C (L.val.adjugate i 0) * X 0 + MvPolynomial.C (L.val.adjugate i 1) * X 1) := by
    simp [binaryMatrixSubst,Matrix.inv_def,
      Ring.inverse_eq_inv,Fin.sum_univ_two,smul_eq_mul,map_mul,mul_add,mul_assoc]
  have h0 := hx 0
  have h1 := hx 1
  simp only [Matrix.adjugate_fin_two,Matrix.of_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_neg] at h0 h1
  rw [h0,h1]
  ring

end TernaryPoly.SymmetricLineCohomology
