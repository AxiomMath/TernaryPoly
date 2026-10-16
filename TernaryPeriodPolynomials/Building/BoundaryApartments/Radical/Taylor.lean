module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Radical
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

theorem polynomialTaylor_finite (polynomial : Polynomial ℂ) (bound : ℕ)
    (degree_lt : polynomial.natDegree < bound) (point shift : ℂ) :
    polynomial.eval (point + shift) =
      ∑ iterations ∈ Finset.range bound,
        ((iterations.factorial : ℂ)⁻¹ * shift ^ iterations) *
          (((fun value : Polynomial ℂ => value.derivative)^[iterations]) polynomial).eval point := by
  rw [add_comm point shift, ← Polynomial.taylor_eval point polynomial shift]
  rw [Polynomial.eval_eq_sum_range' (by simpa only [Polynomial.natDegree_taylor] using degree_lt)]
  apply Finset.sum_congr rfl
  intro iterations _
  rw [Polynomial.taylor_coeff]
  have differentiated := congrFun (Polynomial.factorial_smul_hasseDeriv
    (R := ℂ) iterations) polynomial
  change iterations.factorial • ((Polynomial.hasseDeriv iterations) polynomial) = _
    at differentiated
  have evaluated := congrArg (Polynomial.eval point) differentiated
  simp only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast] at evaluated
  rw [← evaluated]
  have factorial_nonzero : (iterations.factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr iterations.factorial_ne_zero
  field_simp

def firstVariablePolynomial (polynomial : Poly) (second third : ℂ) : Polynomial ℂ :=
  Polynomial.map (eval ![second, third]) (finSuccEquiv ℂ 2 polynomial)

theorem firstVariablePolynomial_C (coefficient second third : ℂ) :
    firstVariablePolynomial (C coefficient) second third = Polynomial.C coefficient := by
  simp [firstVariablePolynomial, finSuccEquiv_apply]

theorem firstVariablePolynomial_X (index : Fin 3) (second third : ℂ) :
    firstVariablePolynomial (X index) second third =
      (![Polynomial.X, Polynomial.C second, Polynomial.C third] index) := by
  fin_cases index
  · simp [firstVariablePolynomial, finSuccEquiv_X_zero]
  · change firstVariablePolynomial (X (0 : Fin 2).succ) second third = _
    unfold firstVariablePolynomial
    rw [finSuccEquiv_X_succ (j := (0 : Fin 2))]
    simp
  · change firstVariablePolynomial (X (1 : Fin 2).succ) second third = _
    unfold firstVariablePolynomial
    rw [finSuccEquiv_X_succ (j := (1 : Fin 2))]
    simp

theorem firstVariablePolynomial_add (first second : Poly) (left right : ℂ) :
    firstVariablePolynomial (first + second) left right =
      firstVariablePolynomial first left right + firstVariablePolynomial second left right := by
  simp [firstVariablePolynomial]

theorem firstVariablePolynomial_mul (first second : Poly) (left right : ℂ) :
    firstVariablePolynomial (first * second) left right =
      firstVariablePolynomial first left right * firstVariablePolynomial second left right := by
  simp [firstVariablePolynomial]

theorem firstVariablePolynomial_eval (polynomial : Poly) (first second third : ℂ) :
    Polynomial.eval first (firstVariablePolynomial polynomial second third) =
      polynomialValue polynomial first second third := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient => simp [firstVariablePolynomial_C, polynomialValue]
  | add left right left_eq right_eq =>
    simp only [firstVariablePolynomial_add, Polynomial.eval_add, polynomialValue, map_add] at *
    rw [left_eq, right_eq]
  | mul_X polynomial index induction_hypothesis =>
    rw [firstVariablePolynomial_mul, Polynomial.eval_mul,
      induction_hypothesis, firstVariablePolynomial_X]
    fin_cases index <;> simp [polynomialValue]

theorem firstVariablePolynomial_pderiv (polynomial : Poly) (second third : ℂ) :
    firstVariablePolynomial (pderiv 0 polynomial) second third =
      Polynomial.derivative (firstVariablePolynomial polynomial second third) := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
    rw [pderiv_C, firstVariablePolynomial_C, Polynomial.derivative_C]
    simp [firstVariablePolynomial]
  | add left right left_eq right_eq =>
    rw [map_add, firstVariablePolynomial_add, left_eq, right_eq,
      firstVariablePolynomial_add, Polynomial.derivative_add]
  | mul_X polynomial index induction_hypothesis =>
    rw [pderiv_mul, firstVariablePolynomial_add, firstVariablePolynomial_mul,
      firstVariablePolynomial_mul, induction_hypothesis]
    rw [firstVariablePolynomial_mul, Polynomial.derivative_mul]
    congr 1
    rw [firstVariablePolynomial_X]
    fin_cases index <;> simp [firstVariablePolynomial]

theorem firstVariablePolynomial_iterate (iterations : ℕ) (polynomial : Poly) (second third : ℂ) :
    firstVariablePolynomial
      (((fun value : Poly => pderiv 0 value)^[iterations]) polynomial) second third =
      ((fun value : Polynomial ℂ => value.derivative)^[iterations])
        (firstVariablePolynomial polynomial second third) := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    rw [Function.iterate_succ_apply', firstVariablePolynomial_pderiv,
      induction_hypothesis, Function.iterate_succ_apply']

theorem firstVariablePolynomial_degree {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (second third : ℂ) :
    (firstVariablePolynomial polynomial.val second third).natDegree ≤ degree := by
  exact Polynomial.natDegree_map_le.trans (by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans polynomial.property.totalDegree_le)

theorem radicalTaylor_eval {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (first second third shift : ℂ) :
    polynomialValue polynomial.val (first + shift) second third =
      ∑ iterations ∈ Finset.range (degree + 1),
        ((iterations.factorial : ℂ)⁻¹ * shift ^ iterations) *
          polynomialValue (((fun value : Poly => pderiv 0 value)^[iterations]) polynomial.val)
            first second third := by
  have expansion := polynomialTaylor_finite
    (firstVariablePolynomial polynomial.val second third) (degree + 1)
    (Nat.lt_succ_of_le (firstVariablePolynomial_degree polynomial second third)) first shift
  simpa only [← firstVariablePolynomial_iterate, firstVariablePolynomial_eval] using expansion

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
