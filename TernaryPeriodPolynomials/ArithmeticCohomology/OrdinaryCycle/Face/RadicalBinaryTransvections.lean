module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantPlaneInvariants
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyPolynomials

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RelativeStabilizerParameters RelativeStabilizerMatrices
open RelativeEdgeCohomologyPolynomials

/-- Binary root substitution is polynomial translation for every rational step. -/
theorem binary_finSucc_shearStep (t : ℚ) (p : MvPolynomial (Fin 2) ℚ) :
    finSuccEquiv ℚ 1 (bind₁ ![X 0-C t*X 1,X 1] p) =
      Polynomial.taylor (-(C t*X (0 : Fin 1))) (finSuccEquiv ℚ 1 p) := by
  have hx : finSuccEquiv ℚ 1 (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) := by
    simpa using (finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := (0 : Fin 1)))
  have hc : finSuccEquiv ℚ 1 (C t : MvPolynomial (Fin 2) ℚ)=Polynomial.C (C t) := by
    simp [finSuccEquiv_apply]
  induction p using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.taylor_mul,hp]
    fin_cases i <;> simp [finSuccEquiv_X_zero,hx,hc,sub_eq_add_neg]

/-- A nonzero binary root step has the same fixed axis as the full root group. -/
theorem binary_shearStep_fixed_axis (t : ℚ) (ht : t≠0) (p : MvPolynomial (Fin 2) ℚ)
    (hp : bind₁ ![X 0-C t*X 1,X 1] p=p) :
    p=rename Fin.succ ((finSuccEquiv ℚ 1 p).coeff 0) := by
  have hh := congrArg (finSuccEquiv ℚ 1) hp
  rw [binary_finSucc_shearStep] at hh
  have hc := polynomial_eq_constant_of_translation (finSuccEquiv ℚ 1 p)
    (-(C t*X (0 : Fin 1)))
    (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr ht) (X_ne_zero 0))) hh
  have he (q : MvPolynomial (Fin 1) ℚ) :
      finSuccEquiv ℚ 1 (rename Fin.succ q)=Polynomial.C q := by
    induction q using MvPolynomial.induction_on with
    | C r => simp [finSuccEquiv_apply]
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p i hp => simp only [map_mul,rename_X,finSuccEquiv_X_succ,hp]
  exact (finSuccEquiv ℚ 1).injective (hc.trans (he _).symm)

/-- Two opposite nonzero root steps have no positive-degree binary homogeneous invariants. -/
theorem binary_transvectionSteps_fixed_zero {n : ℕ} (hn : 0<n)
    (t u : ℚ) (ht : t≠0) (hu : u≠0) (p : BinaryH n)
    (h₁ : bind₁ ![X 0-C t*X 1,X 1] (p : MvPolynomial (Fin 2) ℚ)=(p : MvPolynomial (Fin 2) ℚ))
    (h₂ : bind₁ ![X 0,X 1-C u*X 0] (p : MvPolynomial (Fin 2) ℚ)=(p : MvPolynomial (Fin 2) ℚ)) : p=0 := by
  let q : UnaryH n := ⟨(finSuccEquiv ℚ 1 p).coeff 0,
    p.property.finSuccEquiv_coeff_isHomogeneous 0 n (by omega)⟩
  have hp := binary_shearStep_fixed_axis t ht p h₁
  have hq := unary_homogeneous_eq n q
  have hshape : (p : MvPolynomial (Fin 2) ℚ)=X 1^n*C (unaryScalarEquiv n q) := by
    rw [hp]
    change rename Fin.succ (q : MvPolynomial (Fin 1) ℚ)=_
    rw [hq]
    have hm : monomial (Finsupp.single (0 : Fin 1) n) (unaryScalarEquiv n q)=
        X 0^n*C (unaryScalarEquiv n q) := by
      simpa using (monomial_single_add (n := (0 : Fin 1)) (e := n) (s := 0)
        (a := unaryScalarEquiv n q))
    change rename Fin.succ (monomial (Finsupp.single (0 : Fin 1) n) (unaryScalarEquiv n q))=_
    rw [hm]
    simp
  have hc := congrArg (eval (![1,0] : Fin 2 → ℚ)) h₂
  rw [hshape] at hc
  have hc' : unaryScalarEquiv n q=0 := by
    have hz : (-u)^n*unaryScalarEquiv n q=0 := by simpa [hn.ne'] using hc
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hu))
  apply Subtype.ext
  change (p : MvPolynomial (Fin 2) ℚ)=0
  rw [hshape,hc',map_zero,mul_zero]

def binaryUpperMatrix (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := ![![1,k],![0,1]]

def binaryLowerMatrix (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := ![![1,0],![k,1]]

/-- Integral upper transvection with its actual integer step. -/
def binaryUpperStep (k : ℤ) : GL2 where
  val := binaryUpperMatrix k
  inv := binaryUpperMatrix (-k)
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [binaryUpperMatrix,Fin.sum_univ_two]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [binaryUpperMatrix,Fin.sum_univ_two]

/-- Integral lower transvection with its actual integer step. -/
def binaryLowerStep (k : ℤ) : GL2 where
  val := binaryLowerMatrix k
  inv := binaryLowerMatrix (-k)
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [binaryLowerMatrix,Fin.sum_univ_two]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [binaryLowerMatrix,Fin.sum_univ_two]

theorem binaryUpperStep_substitute (k : ℤ) :
    binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) (binaryUpperStep k)⁻¹).val =
      bind₁ ![X 0-C (k : ℚ)*X 1,X 1] := by
  have hv : ((binaryUpperStep k)⁻¹).val = ![![1,-k],![0,1]] := rfl
  have hm : (GeneralLinearGroup.map (Int.castRingHom ℚ) (binaryUpperStep k)⁻¹).val =
      (![![1,-(k : ℚ)],![0,1]] : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    rw [GeneralLinearGroup.map_apply]
    change (((binaryUpperStep k)⁻¹).val i j : ℚ)=_
    rw [hv]
    fin_cases i <;> fin_cases j <;> simp
  rw [hm]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [binaryMatrixSubst,Fin.sum_univ_two,sub_eq_add_neg]

theorem binaryLowerStep_substitute (k : ℤ) :
    binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) (binaryLowerStep k)⁻¹).val =
      bind₁ ![X 0,X 1-C (k : ℚ)*X 0] := by
  have hv : ((binaryLowerStep k)⁻¹).val = ![![1,0],![-k,1]] := rfl
  have hm : (GeneralLinearGroup.map (Int.castRingHom ℚ) (binaryLowerStep k)⁻¹).val =
      (![![1,0],![-(k : ℚ),1]] : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    rw [GeneralLinearGroup.map_apply]
    change (((binaryLowerStep k)⁻¹).val i j : ℚ)=_
    rw [hv]
    fin_cases i <;> fin_cases j <;> simp
  rw [hm]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [binaryMatrixSubst,Fin.sum_univ_two,sub_eq_add_neg,add_comm]

end TernaryPoly.OrdinaryFaceRadical
