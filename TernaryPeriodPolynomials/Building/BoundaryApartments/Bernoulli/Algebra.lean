module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Homogeneous

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open MvPolynomial

theorem derivative_iterate_add (iterations : ℕ) (first second : Poly) :
    ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) (first + second) =
      ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) first +
        ((fun polynomial : Poly => pderiv 0 polynomial)^[iterations]) second := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    simp only [Function.iterate_succ_apply', induction_hypothesis, map_add]

theorem derivative_iterate_smul (iterations : ℕ) (scalar : ℂ) (polynomial : Poly) :
    ((fun value : Poly => pderiv 0 value)^[iterations]) (scalar • polynomial) =
      scalar • ((fun value : Poly => pderiv 0 value)^[iterations]) polynomial := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    simp only [Function.iterate_succ_apply', induction_hypothesis]
    simpa only [MvPolynomial.smul_eq_C_mul] using pderiv_C_mul

theorem bernoulliOperator_add (degree : ℕ) (parameter first second : Poly) :
    bernoulliOperator degree parameter (first + second) =
      bernoulliOperator degree parameter first + bernoulliOperator degree parameter second := by
  simp only [bernoulliOperator, derivative_iterate_add, mul_add, Finset.sum_add_distrib]

theorem bernoulliOperator_smul (degree : ℕ) (parameter polynomial : Poly) (scalar : ℂ) :
    bernoulliOperator degree parameter (scalar • polynomial) =
      scalar • bernoulliOperator degree parameter polynomial := by
  simp only [bernoulliOperator, derivative_iterate_smul, mul_smul_comm,
    Finset.smul_sum]

def bernoulliLinearMap (degree : ℕ) (parameter : Poly) : Poly →ₗ[ℂ] Poly where
  toFun := bernoulliOperator degree parameter
  map_add' := bernoulliOperator_add degree parameter
  map_smul' := fun scalar polynomial => bernoulliOperator_smul degree parameter polynomial scalar

theorem derivative_iterate_mul_constant (iterations : ℕ) (constant polynomial : Poly)
    (constant_derivative : pderiv 0 constant = 0) :
    ((fun value : Poly => pderiv 0 value)^[iterations]) (constant * polynomial) =
      constant * ((fun value : Poly => pderiv 0 value)^[iterations]) polynomial := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    simp only [Function.iterate_succ_apply', induction_hypothesis, pderiv_mul,
      constant_derivative, zero_mul, zero_add]

theorem bernoulliOperator_mul_constant (degree : ℕ) (parameter constant polynomial : Poly)
    (constant_derivative : pderiv 0 constant = 0) :
    bernoulliOperator degree parameter (constant * polynomial) =
      constant * bernoulliOperator degree parameter polynomial := by
  simp only [bernoulliOperator, derivative_iterate_mul_constant _ _ _ constant_derivative,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro iterations _
  ring

theorem derivative_bernoulliOperator (degree : ℕ) (parameter polynomial : Poly)
    (parameter_derivative : pderiv 0 parameter = 0) :
    pderiv 0 (bernoulliOperator degree parameter polynomial) =
      bernoulliOperator degree parameter (pderiv 0 polynomial) := by
  have power_derivative (iterations : ℕ) : pderiv 0 ((-parameter) ^ iterations) = 0 := by
    simp [map_neg, parameter_derivative]
  simp only [bernoulliOperator, map_sum]
  apply Finset.sum_congr rfl
  intro iterations _
  rw [mul_assoc, pderiv_C_mul, pderiv_mul, power_derivative, zero_mul, zero_add]
  rw [mul_assoc]
  congr 2
  exact Function.iterate_succ_apply' (fun value : Poly => pderiv 0 value) iterations polynomial |>.symm.trans
    (Function.iterate_succ_apply (fun value : Poly => pderiv 0 value) iterations polynomial)

theorem derivative_iterate_bernoulliOperator (iterations degree : ℕ)
    (parameter polynomial : Poly) (parameter_derivative : pderiv 0 parameter = 0) :
    ((fun value : Poly => pderiv 0 value)^[iterations])
        (bernoulliOperator degree parameter polynomial) =
      bernoulliOperator degree parameter
        (((fun value : Poly => pderiv 0 value)^[iterations]) polynomial) := by
  induction iterations with
  | zero => rfl
  | succ iterations induction_hypothesis =>
    simp only [Function.iterate_succ_apply', induction_hypothesis,
      derivative_bernoulliOperator _ _ _ parameter_derivative]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
