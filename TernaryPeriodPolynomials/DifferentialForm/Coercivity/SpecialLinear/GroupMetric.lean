module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Metric
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section


/-! Finite matrix substitution preserves the factorial metric for orthogonal matrices. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

def realLinearForm (A : Mat) (i : Fin 3) : Poly := ∑ j, C (A i j) * X j

def realSubstitute (A : Mat) : Poly →ₐ[ℝ] Poly := bind₁ (realLinearForm A)

@[simp] theorem realSubstitute_X (A : Mat) (i : Fin 3) :
    realSubstitute A (X i) = realLinearForm A i := by simp [realSubstitute]

@[simp] theorem realSubstitute_C (A : Mat) (r : ℝ) :
    realSubstitute A (C r) = C r := by simp [realSubstitute]

theorem realSubstitute_linearForm (A B : Mat) (i : Fin 3) :
    realSubstitute A (realLinearForm B i) = realLinearForm (B * A) i := by
  simp only [realLinearForm, map_sum, map_mul, realSubstitute_C, realSubstitute_X,
    Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem realSubstitute_comp (A B : Mat) :
    (realSubstitute A).comp (realSubstitute B) = realSubstitute (B * A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa only [AlgHom.comp_apply, realSubstitute_X] using realSubstitute_linearForm A B i

theorem realSubstitute_one : realSubstitute (1 : Mat) = AlgHom.id ℝ Poly := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [realLinearForm, Matrix.one_apply]

theorem constantCoeff_realSubstitute (A : Mat) (p : Poly) :
    constantCoeff (realSubstitute A p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [realLinearForm]

theorem pderiv_realLinearForm (A : Mat) (i j : Fin 3) :
    pderiv i (realLinearForm A j) = C (A j i) := by
  fin_cases i <;> simp [realLinearForm, Fin.sum_univ_succ]

theorem pderiv_realSubstitute (A : Mat) (i : Fin 3) (p : Poly) :
    pderiv i (realSubstitute A p) = ∑ j : Fin 3, C (A j i) * realSubstitute A (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, realSubstitute_X, pderiv_mul, hp, pderiv_realLinearForm,
      map_add, Finset.sum_mul]
    fin_cases k <;> simp [Fin.sum_univ_succ] <;> ring

/-- Full finite matrix transpose-adjoint identity, stronger than infinitesimal admissibility. -/
theorem realSubstitute_transpose_adjoint (A : Mat) (p q : Poly) :
    factorialPairing (realSubstitute A p) q = factorialPairing p (realSubstitute A.transpose q) := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C r =>
    rw [realSubstitute_C]
    simp only [C_apply, factorialPairing_monomial]
    change r * factorialWeight 0 * constantCoeff q =
      r * factorialWeight 0 * constantCoeff (realSubstitute A.transpose q)
    rw [constantCoeff_realSubstitute]
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp =>
    rw [map_mul, realSubstitute_X, realLinearForm, Finset.mul_sum]
    simp only [map_sum, LinearMap.sum_apply]
    have hterm (j : Fin 3) : factorialPairing (realSubstitute A p * (C (A i j) * X j)) q =
        A i j * factorialPairing p (realSubstitute A.transpose (pderiv j q)) := by
      rw [show realSubstitute A p * (C (A i j) * X j) =
        A i j • (X j * realSubstitute A p) by rw [smul_eq_C_mul]; ring]
      rw [map_smul, LinearMap.smul_apply, factorialPairing_X_mul, hp]
      rfl
    simp_rw [hterm]
    rw [mul_comm p (X i), factorialPairing_X_mul, pderiv_realSubstitute]
    simp [Matrix.transpose_apply, ← smul_eq_C_mul]

theorem realSubstitute_orthogonal_invariant (A : Mat) (hA : A * A.transpose = 1)
    (p q : Poly) :
    factorialPairing (realSubstitute A p) (realSubstitute A q) = factorialPairing p q := by
  rw [realSubstitute_transpose_adjoint]
  have h := congrArg (fun F : Poly →ₐ[ℝ] Poly => F q) (realSubstitute_comp A.transpose A)
  simp only [AlgHom.comp_apply] at h
  rw [h, hA, realSubstitute_one]
  rfl

theorem realLinearForm_homogeneous (A : Mat) (i : Fin 3) :
    (realLinearForm A i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact (isHomogeneous_X (i := j) (R := ℝ)).C_mul _

theorem realSubstitute_preserves_degree (A : Mat) {n : ℕ} {p : Poly}
    (hp : p.IsHomogeneous n) : (realSubstitute A p).IsHomogeneous n := by
  simpa only [realSubstitute, one_mul, aeval_eq_bind₁] using hp.aeval (realLinearForm A) (realLinearForm_homogeneous A)

end TernaryPoly.SL3PolynomialCoercivity
