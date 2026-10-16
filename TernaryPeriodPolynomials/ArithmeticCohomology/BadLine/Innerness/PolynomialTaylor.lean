module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BernoulliOperators
public import Mathlib.Algebra.Polynomial.Taylor

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem polynomial_hasse_eval {R : Type*} [CommRing R] [Algebra ℂ R]
    (p : Polynomial R) (k : ℕ) (x : R) :
    ((Polynomial.hasseDeriv k) p).eval x =
      (k.factorial : ℂ)⁻¹ • (((fun q : Polynomial R => q.derivative)^[k]) p).eval x := by
  have relation := congrArg (Polynomial.eval x)
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R := R) k) p)
  simp only [LinearMap.smul_apply, Polynomial.eval_smul] at relation
  rw [← Nat.cast_smul_eq_nsmul ℂ] at relation
  have nonzero : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have scaled := congrArg (fun v : R => (k.factorial : ℂ)⁻¹ • v) relation
  simpa only [smul_smul, inv_mul_cancel₀ nonzero, one_smul] using scaled

theorem polynomial_taylor_sum {R : Type*} [CommRing R] [Algebra ℂ R]
    (p : Polynomial R) (n : ℕ) (bound : p.natDegree ≤ n) (x y : R) :
    p.eval (x+y) = ∑ k ∈ Finset.range (n+1),
      (k.factorial : ℂ)⁻¹ • ((((fun q : Polynomial R => q.derivative)^[k]) p).eval x * y^k) := by
  have expansion := (Polynomial.taylor x p).as_sum_range' (n+1)
    (by rw [Polynomial.natDegree_taylor]; omega)
  have evaluated := congrArg (Polynomial.eval y) expansion
  simp only [Polynomial.taylor_eval, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Polynomial.taylor_coeff, polynomial_hasse_eval,
    smul_mul_assoc] at evaluated
  simpa only [add_comm] using evaluated

/-- Regard the first variable as the univariate indeterminate, retaining the others. -/
def firstPolynomial : Poly →ₐ[ℂ] Polynomial Poly :=
  (Polynomial.mapAlgHom (rename (Fin.succ : Fin 2 → Fin 3))).comp
    (finSuccEquiv ℂ 2).toAlgHom

theorem firstPolynomial_C (a : ℂ) :
    firstPolynomial (C a) = Polynomial.C (C a) := by
  simp [firstPolynomial]

theorem firstPolynomial_X (i : Fin 3) :
    firstPolynomial (X i) = ![Polynomial.X, Polynomial.C (X 1), Polynomial.C (X 2)] i := by
  fin_cases i
  · simp [firstPolynomial, finSuccEquiv_X_zero]
  · change Polynomial.map _ ((finSuccEquiv ℂ 2) (X (0 : Fin 2).succ)) = _
    rw [finSuccEquiv_X_succ]
    simp
  · change Polynomial.map _ ((finSuccEquiv ℂ 2) (X (1 : Fin 2).succ)) = _
    rw [finSuccEquiv_X_succ]
    simp

theorem firstPolynomial_eval (p : Poly) (x : Poly) :
    (firstPolynomial p).eval x = bind₁ ![x,X 1,X 2] p := by
  have hom_eq : ((Polynomial.aeval x).restrictScalars ℂ).comp firstPolynomial =
      bind₁ ![x,X 1,X 2] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [firstPolynomial_X]
  exact congrArg (fun hom : Poly →ₐ[ℂ] Poly => hom p) hom_eq

theorem firstPolynomial_eval_X (p : Poly) : (firstPolynomial p).eval (X 0) = p := by
  rw [firstPolynomial_eval]
  have variable_eq : ![X 0,X 1,X 2] = (X : Fin 3 → Poly) := by
    funext i
    fin_cases i <;> rfl
  simp only [variable_eq, bind₁_X_left, AlgHom.id_apply]

theorem firstPolynomial_pderiv (p : Poly) :
    firstPolynomial (pderiv 0 p) = (firstPolynomial p).derivative := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [pderiv_mul, map_add, map_mul, Polynomial.derivative_mul, hp]
    congr 1
    fin_cases i <;> simp [firstPolynomial_X]

theorem firstPolynomial_iterate_pderiv (p : Poly) (k : ℕ) :
    firstPolynomial (((fun q : Poly => pderiv 0 q)^[k]) p) =
      ((fun q : Polynomial Poly => q.derivative)^[k]) (firstPolynomial p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', firstPolynomial_pderiv, ih,
      Function.iterate_succ_apply']

theorem firstPolynomial_degree {n : ℕ} (p : HomogeneousPoly n) :
    (firstPolynomial p.val).natDegree ≤ n := by
  change (Polynomial.map _ ((finSuccEquiv ℂ 2) p.val)).natDegree ≤ n
  calc
    _ ≤ ((finSuccEquiv ℂ 2) p.val).natDegree := Polynomial.natDegree_map_le
    _ = degreeOf 0 p.val := natDegree_finSuccEquiv p.val
    _ ≤ p.val.totalDegree := degreeOf_le_totalDegree p.val 0
    _ ≤ n := p.property.totalDegree_le

theorem homogeneous_translation_taylor {n : ℕ} (p : HomogeneousPoly n) (t : Poly) :
    bind₁ ![X 0-t,X 1,X 2] p.val =
      ∑ k ∈ Finset.range (n+1),
        (k.factorial : ℂ)⁻¹ • ((-t)^k * ((fun q : Poly => pderiv 0 q)^[k]) p.val) := by
  have expansion := polynomial_taylor_sum (firstPolynomial p.val) n
    (firstPolynomial_degree p) (X 0) (-t)
  rw [← sub_eq_add_neg, firstPolynomial_eval] at expansion
  simp only [← firstPolynomial_iterate_pderiv, firstPolynomial_eval_X] at expansion
  simpa only [mul_comm] using expansion

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
