module

public import TernaryPeriodPolynomials.AlternatingSolution.Todd
public import TernaryPeriodPolynomials.AlternatingSolution.Todd.Commutator

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

abbrev ToddCoefficient := MvPolynomial (Fin 2) ℚ

/-- Differentiate the coefficient polynomials while fixing the univariate variable. -/
def coefficientPDeriv (i : Fin 2) :
    Polynomial ToddCoefficient →ₗ[ℚ] Polynomial ToddCoefficient :=
  Polynomial.lsum fun n =>
    ((Polynomial.monomial n).restrictScalars ℚ).comp (pderiv i).toLinearMap

@[simp] theorem coefficientPDeriv_monomial (i : Fin 2) (n : ℕ) (r : ToddCoefficient) :
    coefficientPDeriv i (Polynomial.monomial n r) = Polynomial.monomial n (pderiv i r) := by
  simp [coefficientPDeriv, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

@[simp] theorem coefficientPDeriv_coeff (i : Fin 2) (p : Polynomial ToddCoefficient) (n : ℕ) :
    (coefficientPDeriv i p).coeff n = pderiv i (p.coeff n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial m r =>
    rw [coefficientPDeriv_monomial]
    simp only [Polynomial.coeff_monomial]
    split_ifs <;> simp

@[simp] theorem coefficientPDeriv_C (i : Fin 2) (r : ToddCoefficient) :
    coefficientPDeriv i (Polynomial.C r) = Polynomial.C (pderiv i r) := by
  exact coefficientPDeriv_monomial i 0 r

/-- Coefficient differentiation obeys the scalar product rule. -/
theorem coefficientPDeriv_smul (i : Fin 2) (r : ToddCoefficient)
    (p : Polynomial ToddCoefficient) :
    coefficientPDeriv i (r • p) = (pderiv i r) • p + r • coefficientPDeriv i p := by
  ext n
  simp only [coefficientPDeriv_coeff, Polynomial.coeff_add, Polynomial.coeff_smul,
    smul_eq_mul, pderiv_mul]

/-- Coefficient differentiation fixes multiplication by the univariate variable. -/
theorem coefficientPDeriv_mul_X (i : Fin 2) (p : Polynomial ToddCoefficient) :
    coefficientPDeriv i (p * Polynomial.X) = coefficientPDeriv i p * Polynomial.X := by
  ext n
  cases n with
  | zero => simp only [coefficientPDeriv_coeff, Polynomial.coeff_mul_X_zero, map_zero]
  | succ n => simp only [coefficientPDeriv_coeff, Polynomial.coeff_mul_X]

/-- Product rule for multiplication by a coefficient constant. -/
theorem coefficientPDeriv_mul_C (i : Fin 2) (p : Polynomial ToddCoefficient)
    (r : ToddCoefficient) :
    coefficientPDeriv i (p * Polynomial.C r) =
      coefficientPDeriv i p * Polynomial.C r + p * Polynomial.C (pderiv i r) := by
  ext n
  simp only [coefficientPDeriv_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_add,
    pderiv_mul]

/-- Coefficient differentiation does not increase the univariate degree. -/
theorem natDegree_coefficientPDeriv_le (i : Fin 2) (p : Polynomial ToddCoefficient) :
    (coefficientPDeriv i p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coefficientPDeriv_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hn, map_zero]

/-- Hasse differentiation commutes with coefficient differentiation. -/
theorem coefficientPDeriv_hasseDeriv (i : Fin 2) (k : ℕ)
    (p : Polynomial ToddCoefficient) :
    coefficientPDeriv i (Polynomial.hasseDeriv k p) =
      Polynomial.hasseDeriv k (coefficientPDeriv i p) := by
  ext n
  simp only [coefficientPDeriv_coeff, Polynomial.hasseDeriv_coeff, pderiv_mul,
    Derivation.map_natCast, zero_mul, zero_add]

/-- The other two ternary partial derivatives act on the coefficient variables. -/
theorem finSuccEquiv_pderiv_succ (i : Fin 2) (f : TernaryPolynomial) :
    finSuccEquiv ℚ 2 (pderiv i.succ f) =
      coefficientPDeriv i (finSuccEquiv ℚ 2 f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    cases j using Fin.cases with
    | zero =>
      simp [map_mul, hp, finSuccEquiv_X_zero, coefficientPDeriv_mul_X]
      ring
    | succ j =>
      by_cases hij : i = j
      · subst j
        simp [map_mul, hp, finSuccEquiv_X_succ,
          coefficientPDeriv_mul_C, pderiv_X]
        ring
      · simp [map_mul, hp, finSuccEquiv_X_succ,
          coefficientPDeriv_mul_C, pderiv_X, Ne.symm hij]
        ring

/-- The parameter contribution to coefficient differentiation is a finite Hasse sum. -/
theorem coefficientPDeriv_todd_sub (i : Fin 2) (u : ToddCoefficient)
    (p : Polynomial ToddCoefficient) (N : ℕ) (hN : p.natDegree < N) :
    coefficientPDeriv i (todd u p) - todd u (coefficientPDeriv i p) =
      ∑ k ∈ Finset.range N, pderiv i (toddCoeff u k) • Polynomial.hasseDeriv k p := by
  rw [todd_eq_cutoff u p N hN,
    todd_eq_cutoff u (coefficientPDeriv i p) N
      (lt_of_le_of_lt (natDegree_coefficientPDeriv_le i p) hN),
    toddCutoff_apply, toddCutoff_apply, map_sum]
  simp only [coefficientPDeriv_smul, coefficientPDeriv_hasseDeriv,
    Finset.sum_add_distrib, add_sub_cancel_right]

/-- The scalar Euler identity for the coefficient of each Todd Hasse derivative. -/
theorem X_mul_pderiv_toddCoeff (i : Fin 2) (k : ℕ) :
    (X i : ToddCoefficient) * pderiv i (toddCoeff (X i) k) =
      (k : ToddCoefficient) * toddCoeff (X i) k := by
  cases k with
  | zero => simp [toddCoeff]
  | succ k =>
    simp only [toddCoeff, MvPolynomial.algebraMap_eq, pderiv_mul, pderiv_C,
      zero_mul, zero_add, pderiv_pow, map_neg, pderiv_X_self, Nat.add_sub_cancel]
    rw [pow_succ]
    push_cast
    ring

/-- A Todd coefficient is independent of the other coefficient variable. -/
theorem pderiv_toddCoeff_of_ne (i j : Fin 2) (hij : i ≠ j) (k : ℕ) :
    pderiv i (toddCoeff (X j : ToddCoefficient) k) = 0 := by
  simp [toddCoeff, MvPolynomial.algebraMap_eq, pderiv_X, Ne.symm hij]

/-- Hasse differentiation of an `X`-multiple has precisely one lower-order term. -/
theorem hasseDeriv_succ_X_mul {R : Type*} [CommRing R] (k : ℕ) (p : Polynomial R) :
    Polynomial.hasseDeriv (k+1) (Polynomial.X*p) =
      Polynomial.X * Polynomial.hasseDeriv (k+1) p + Polynomial.hasseDeriv k p := by
  ext n
  rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_add]
  cases n with
  | zero =>
    simp [Polynomial.coeff_X_mul, Polynomial.hasseDeriv_coeff]
  | succ n =>
    simp only [Polynomial.coeff_X_mul, Polynomial.hasseDeriv_coeff]
    rw [show n+1+(k+1) = (n+k+1)+1 by omega,
      show n+1+k = n+k+1 by omega,
      show n+(k+1) = n+k+1 by omega, Nat.choose_succ_succ']
    simp only [Nat.cast_add, add_mul, Polynomial.coeff_X_mul]
    ring

/-- A Hasse derivative of the ordinary derivative is the next Hasse derivative with its index. -/
theorem hasseDeriv_derivative_eq_smul {R : Type*} [CommRing R]
    (k : ℕ) (p : Polynomial R) :
    Polynomial.hasseDeriv k (Polynomial.derivative p) =
      (k+1 : R) • Polynomial.hasseDeriv (k+1) p := by
  have h := DFunLike.congr_fun (Polynomial.hasseDeriv_comp (R := R) k 1) p
  rw [show (k+1 : R) = ((k+1 : ℕ) : R) by simp, Nat.cast_smul_eq_nsmul]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Polynomial.hasseDeriv_one',
    Nat.choose_succ_self_right] using h

/-- The commutator on an ordinary derivative is the weighted finite Hasse sum. -/
theorem toddXComm_derivative_sum {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (p : Polynomial R) (N : ℕ)
    (hX : (Polynomial.X * Polynomial.derivative p).natDegree < N)
    (hD : (Polynomial.derivative p).natDegree < N) :
    toddXComm u (Polynomial.derivative p) =
      ∑ k ∈ Finset.range N, toddCoeff u k • ((k : R) • Polynomial.hasseDeriv k p) := by
  rw [toddXComm, todd_eq_cutoff u _ N hX, todd_eq_cutoff u _ N hD,
    toddCutoff_apply, toddCutoff_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_smul_comm, ← smul_sub]
  congr 1
  cases k with
  | zero => simp
  | succ k =>
    rw [hasseDeriv_succ_X_mul, add_sub_cancel_left, hasseDeriv_derivative_eq_smul]
    simp

/-- Differentiation in the Todd parameter, multiplied by the parameter itself. -/
theorem coefficientPDeriv_todd_parameter (i : Fin 2) (p : Polynomial ToddCoefficient) :
    (X i : ToddCoefficient) •
      (coefficientPDeriv i (todd (X i) p) - todd (X i) (coefficientPDeriv i p)) =
      toddXComm (X i) (Polynomial.derivative p) := by
  let N := p.natDegree + (Polynomial.derivative p).natDegree +
    (Polynomial.X * Polynomial.derivative p).natDegree + 1
  have hN : p.natDegree < N := by dsimp [N]; omega
  have hD : (Polynomial.derivative p).natDegree < N := by dsimp [N]; omega
  have hX : (Polynomial.X * Polynomial.derivative p).natDegree < N := by
    dsimp [N]; omega
  rw [coefficientPDeriv_todd_sub i (X i) p N hN,
    toddXComm_derivative_sum (X i) p N hX hD, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_smul, X_mul_pderiv_toddCoeff, mul_comm]

/-- Coefficient differentiation commutes with Todd in an independent parameter. -/
theorem coefficientPDeriv_todd_of_ne (i j : Fin 2) (hij : i ≠ j)
    (p : Polynomial ToddCoefficient) :
    coefficientPDeriv i (todd (X j) p) = todd (X j) (coefficientPDeriv i p) := by
  apply sub_eq_zero.mp
  rw [coefficientPDeriv_todd_sub i (X j) p (p.natDegree+1) (Nat.lt_succ_self _)]
  simp only [pderiv_toddCoeff_of_ne i j hij, zero_smul, Finset.sum_const_zero]

/-- The scaled `Z`-parameter derivative of ternary Todd is its `X` commutator. -/
theorem ternaryTodd_Z_parameter_derivative (f : TernaryPolynomial) :
    (X 1 : ToddCoefficient) •
      (finSuccEquiv ℚ 2 (pderiv 2 (ternaryTodd (X 1 : ToddCoefficient) f)) -
        todd (X 1 : ToddCoefficient) (finSuccEquiv ℚ 2 (pderiv 2 f))) =
      toddXComm (X 1 : ToddCoefficient) (Polynomial.derivative (finSuccEquiv ℚ 2 f)) := by
  change (X 1 : ToddCoefficient) •
      (finSuccEquiv ℚ 2 (pderiv (1 : Fin 2).succ (ternaryTodd (X 1 : ToddCoefficient) f)) -
        todd (X 1 : ToddCoefficient) (finSuccEquiv ℚ 2 (pderiv (1 : Fin 2).succ f))) = _
  rw [finSuccEquiv_pderiv_succ, finSuccEquiv_pderiv_succ]
  simpa only [ternaryTodd, AlgEquiv.apply_symm_apply] using
    coefficientPDeriv_todd_parameter 1 (finSuccEquiv ℚ 2 f)

/-- The ternary `Z` derivative commutes with Todd whose parameter is `Y`. -/
theorem pderiv_two_ternaryTodd_Y (f : TernaryPolynomial) :
    pderiv 2 (ternaryTodd (X 0 : ToddCoefficient) f) =
      ternaryTodd (X 0 : ToddCoefficient) (pderiv 2 f) := by
  apply (finSuccEquiv ℚ 2).injective
  change finSuccEquiv ℚ 2 (pderiv (1 : Fin 2).succ
      (ternaryTodd (X 0 : ToddCoefficient) f)) = _
  rw [finSuccEquiv_pderiv_succ]
  simp only [ternaryTodd, AlgEquiv.apply_symm_apply]
  rw [coefficientPDeriv_todd_of_ne 1 0 (by decide)]
  exact congrArg (todd (X 0 : ToddCoefficient)) (finSuccEquiv_pderiv_succ 1 f).symm

end TernaryPoly
