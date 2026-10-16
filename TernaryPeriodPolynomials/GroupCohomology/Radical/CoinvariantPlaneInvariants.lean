module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantLevi
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantTwist

@[expose] public section


open MvPolynomial Matrix

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

theorem binary_finSucc_shear (p : MvPolynomial (Fin 2) ℚ) :
    finSuccEquiv ℚ 1 (bind₁ ![X 0-X 1, X 1] p) =
      Polynomial.taylor (-X (0 : Fin 1)) (finSuccEquiv ℚ 1 p) := by
  have hx : finSuccEquiv ℚ 1 (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) := by
    simpa using (finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := (0 : Fin 1)))
  induction p using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.taylor_mul, hp]
    fin_cases i <;> simp [finSuccEquiv_X_zero, hx, sub_eq_add_neg]

/-- Fixed vectors of the first binary transvection are polynomials in the second variable. -/
theorem binary_shear_fixed_axis (p : MvPolynomial (Fin 2) ℚ)
    (hp : bind₁ ![X 0-X 1, X 1] p = p) :
    p = rename Fin.succ ((finSuccEquiv ℚ 1 p).coeff 0) := by
  have ht : Polynomial.taylor (-X (0 : Fin 1)) (finSuccEquiv ℚ 1 p) =
      finSuccEquiv ℚ 1 p := by
    rw [← binary_finSucc_shear, hp]
  have hd := todd_difference (X (0 : Fin 1)) (finSuccEquiv ℚ 1 p)
  rw [ht, sub_self, map_zero] at hd
  have hd' : Polynomial.derivative (finSuccEquiv ℚ 1 p) = 0 := by
    rw [Polynomial.smul_eq_C_mul] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (by simp)
  apply (finSuccEquiv ℚ 1).injective
  rw [Polynomial.eq_C_of_derivative_eq_zero hd']
  have he (q : MvPolynomial (Fin 1) ℚ) :
      finSuccEquiv ℚ 1 (rename Fin.succ q) = Polynomial.C q := by
    induction q using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv_apply]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, rename_X, finSuccEquiv_X_succ, hp]
  rw [he]
  simp

/-- Two binary transvections have no fixed homogeneous vectors in positive degree. -/
theorem binary_transvections_fixed_zero {n : ℕ} (hn : 0 < n) (p : BinaryH n)
    (h₁ : bind₁ ![X 0-X 1, X 1] (p : MvPolynomial (Fin 2) ℚ) = (p : MvPolynomial (Fin 2) ℚ))
    (h₂ : bind₁ ![X 0, X 1-X 0] (p : MvPolynomial (Fin 2) ℚ) = (p : MvPolynomial (Fin 2) ℚ)) : p = 0 := by
  let q : UnaryH n := ⟨(finSuccEquiv ℚ 1 p).coeff 0,
    p.property.finSuccEquiv_coeff_isHomogeneous 0 n (by omega)⟩
  have hp := binary_shear_fixed_axis p h₁
  have hq := unary_homogeneous_eq n q
  have hshape : (p : MvPolynomial (Fin 2) ℚ) =
      X 1 ^ n * C (unaryScalarEquiv n q) := by
    rw [hp]
    change rename Fin.succ (q : MvPolynomial (Fin 1) ℚ) = _
    rw [hq]
    have hm : monomial (Finsupp.single (0 : Fin 1) n) (unaryScalarEquiv n q) =
        X 0 ^ n * C (unaryScalarEquiv n q) := by
      simpa using (monomial_single_add (n := (0 : Fin 1)) (e := n) (s := 0)
        (a := unaryScalarEquiv n q))
    change rename Fin.succ (monomial (Finsupp.single (0 : Fin 1) n) (unaryScalarEquiv n q)) = _
    rw [hm]
    simp
  have hc := congrArg (eval (![1,0] : Fin 2 → ℚ)) h₂
  rw [hshape] at hc
  simp [hn.ne'] at hc
  have hc' : unaryScalarEquiv n q = 0 := by
    rw [hc, map_zero]
  apply Subtype.ext
  change (p : MvPolynomial (Fin 2) ℚ) = 0
  rw [hshape, hc', map_zero, mul_zero]

def binaryUpper : GL2 where
  val := ![![1,1],![0,1]]
  inv := ![![1,-1],![0,1]]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def binaryLower : GL2 where
  val := ![![1,0],![1,1]]
  inv := ![![1,0],![-1,1]]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def binaryReflect : GL2 where
  val := ![![-1,0],![0,1]]
  inv := ![![-1,0],![0,1]]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

theorem binaryUpper_substitute :
    binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryUpper⁻¹).val =
      bind₁ ![X 0-X 1, X 1] := by
  have hv : (binaryUpper⁻¹).val = ![![1,-1],![0,1]] := rfl
  have hm : (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryUpper⁻¹).val =
      (![![1,-1],![0,1]] : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    rw [GeneralLinearGroup.map_apply]
    change ((binaryUpper⁻¹).val i j : ℚ) = _
    rw [hv]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hm]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [binaryMatrixSubst, Fin.sum_univ_two, sub_eq_add_neg]

theorem binaryLower_substitute :
    binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryLower⁻¹).val =
      bind₁ ![X 0, X 1-X 0] := by
  have hv : (binaryLower⁻¹).val = ![![1,0],![-1,1]] := rfl
  have hm : (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryLower⁻¹).val =
      (![![1,0],![-1,1]] : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    rw [GeneralLinearGroup.map_apply]
    change ((binaryLower⁻¹).val i j : ℚ) = _
    rw [hv]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hm]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [binaryMatrixSubst, Fin.sum_univ_two, sub_eq_add_neg, add_comm]

@[simp] theorem planeLeviRootDual_upper : planeLeviRootDual binaryUpper = 1 := by
  unfold planeLeviRootDual
  rw [Matrix.det_fin_two]
  norm_num [binaryUpper]

@[simp] theorem planeLeviRootDual_lower : planeLeviRootDual binaryLower = 1 := by
  unfold planeLeviRootDual
  rw [Matrix.det_fin_two]
  norm_num [binaryLower]

@[simp] theorem planeLeviRootDual_reflect : planeLeviRootDual binaryReflect = -1 := by
  unfold planeLeviRootDual
  rw [Matrix.det_fin_two]
  norm_num [binaryReflect]

/-- The actual GL₂ Levi has no fixed vectors on the determinant-dual-twisted plane quotient. -/
theorem binary_twisted_Levi_fixed_zero (n : ℕ) (p : BinaryH n)
    (hp : ∀ A : GL2, planeLeviRootDual A •
      binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val
        (p : MvPolynomial (Fin 2) ℚ) = (p : MvPolynomial (Fin 2) ℚ)) : p = 0 := by
  by_cases hn : n = 0
  · subst n
    have hc : (p : MvPolynomial (Fin 2) ℚ) = C ((p : MvPolynomial (Fin 2) ℚ).coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero p.property.totalDegree_le)
    have h := hp binaryReflect
    rw [hc] at h
    have hscalar := congrArg (·.coeff (0 : Fin 2 →₀ ℕ)) h
    simp [binaryMatrixSubst] at hscalar
    have hz : (p : MvPolynomial (Fin 2) ℚ).coeff 0 = 0 := by linarith
    apply Subtype.ext
    change (p : MvPolynomial (Fin 2) ℚ) = 0
    rw [hc, hz, map_zero]
  · apply binary_transvections_fixed_zero (Nat.pos_of_ne_zero hn) p
    · have h := hp binaryUpper
      rw [binaryUpper_substitute] at h
      simpa using h
    · have h := hp binaryLower
      rw [binaryLower_substitute] at h
      simpa using h

/-- Vanishing is stated directly for the existing coefficient action and quotient evaluation. -/
theorem plane_twisted_fixed_eq_zero (n : ℕ) (p : H n)
    (hp : ∀ A : GL2, planeLeviRootDual A •
      (planeEval n (PolynomialGLAction.integralAction n 0 (planeElement A 0) p) :
        MvPolynomial (Fin 2) ℚ) = (planeEval n p : MvPolynomial (Fin 2) ℚ)) :
    planeEval n p = 0 := by
  apply binary_twisted_Levi_fixed_zero n (planeEval n p)
  intro A
  rw [← planeEval_Levi]
  exact hp A

end TernaryPoly.RadicalCoinvariantAlgebra
