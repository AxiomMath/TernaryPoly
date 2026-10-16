module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Bernoulli.Algebra
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

theorem polynomial_periodic_eval_constant (polynomial : Polynomial ℂ) (step : ℂ)
    (step_nonzero : step ≠ 0)
    (periodic : ∀ point, polynomial.eval (point + step) = polynomial.eval point)
    (point : ℂ) : polynomial.eval point = polynomial.eval 0 := by
  have values (iterations : ℕ) :
      polynomial.eval ((iterations : ℂ) * step) = polynomial.eval 0 := by
    induction iterations with
    | zero => simp
    | succ iterations induction_hypothesis =>
      rw [show ((iterations + 1 : ℕ) : ℂ) * step = (iterations : ℂ) * step + step by
        push_cast
        ring, periodic, induction_hypothesis]
  have points_injective : Function.Injective (fun iterations : ℕ => (iterations : ℂ) * step) := by
    intro first second equality
    exact Nat.cast_injective (mul_right_cancel₀ step_nonzero equality)
  have constant : polynomial = Polynomial.C (polynomial.eval 0) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective points_injective).mono
    rintro current ⟨iterations, rfl⟩
    simpa using values iterations
  rw [constant]
  simp

def thirdVariablePolynomial (polynomial : Poly) (first second : ℂ) : Polynomial ℂ :=
  eval₂Hom Polynomial.C ![Polynomial.C first, Polynomial.C second, Polynomial.X] polynomial

theorem thirdVariablePolynomial_eval (polynomial : Poly) (first second third : ℂ) :
    Polynomial.eval third (thirdVariablePolynomial polynomial first second) =
      polynomialValue polynomial first second third := by
  unfold thirdVariablePolynomial
  change (Polynomial.evalRingHom third)
    ((eval₂Hom Polynomial.C ![Polynomial.C first, Polynomial.C second, Polynomial.X])
      polynomial) = _
  rw [MvPolynomial.map_eval₂Hom]
  have coefficients : (Polynomial.evalRingHom third).comp Polynomial.C = RingHom.id ℂ := by
    ext coefficient
    simp
  have coordinates :
      (fun index => (Polynomial.evalRingHom third)
        (![Polynomial.C first, Polynomial.C second, Polynomial.X] index)) =
          ![first, second, third] := by
    funext index
    fin_cases index <;> simp
  rw [coefficients, coordinates]
  rfl

theorem binaryShearInvariant_homogeneous {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (binary : ∀ first second third,
      polynomialValue polynomial.val first second third =
        polynomialValue polynomial.val 0 second third)
    (shear : ∀ second third,
      polynomialValue polynomial.val 0 second (third + 3 * second) =
        polynomialValue polynomial.val 0 second third) :
    polynomial.val = C (polynomialValue polynomial.val 0 1 0) * X 1 ^ degree := by
  apply MvPolynomial.funext_set (fun index : Fin 3 =>
    if index = 1 then Set.univ \ {0} else Set.univ)
  · intro index
    split_ifs
    · exact Set.infinite_univ.sdiff (Set.finite_singleton 0)
    · exact Set.infinite_univ
  · intro coordinates coordinates_mem
    have second_nonzero : coordinates 1 ≠ 0 := by
      have membership := coordinates_mem 1 (Set.mem_univ _)
      simpa using membership
    have periodic : ∀ point,
        (thirdVariablePolynomial polynomial.val 0 (coordinates 1)).eval
          (point + 3 * coordinates 1) =
        (thirdVariablePolynomial polynomial.val 0 (coordinates 1)).eval point := by
      intro point
      simpa only [thirdVariablePolynomial_eval] using shear (coordinates 1) point
    have constant := polynomial_periodic_eval_constant
      (thirdVariablePolynomial polynomial.val 0 (coordinates 1)) (3 * coordinates 1)
      (mul_ne_zero (by norm_num) second_nonzero) periodic (coordinates 2)
    simp only [thirdVariablePolynomial_eval] at constant
    have scale := homogeneousValue_scale polynomial (coordinates 1) ![0, 1, 0]
    have scaled_coordinates :
        (fun index => coordinates 1 * (![0, 1, 0] : Fin 3 → ℂ) index) =
          ![0, coordinates 1, 0] := by
      funext index
      fin_cases index <;> simp
    rw [scaled_coordinates] at scale
    have coordinates_eta : coordinates = ![coordinates 0, coordinates 1, coordinates 2] := by
      funext index
      fin_cases index <;> rfl
    rw [coordinates_eta]
    change polynomialValue polynomial.val (coordinates 0) (coordinates 1) (coordinates 2) = _
    rw [binary, constant]
    simp only [map_mul, map_pow, eval_C, eval_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    simpa only [polynomialValue, mul_comm] using scale

theorem binaryDetection_of_primitive {degree : ℕ} {polynomial : Poly}
    (degree_positive : 0 < degree)
    (primitive : HomogeneousPoly degree)
    (binary : ∀ first second third,
      polynomialValue primitive.val first second third =
        polynomialValue primitive.val 0 second third)
    (shear : ∀ second third,
      polynomialValue primitive.val 0 second (third + 3 * second) =
        polynomialValue primitive.val 0 second third)
    (coordinate : polynomial = primitive.val -
      bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] primitive.val)
    (boundary : ∀ first third, polynomialValue polynomial first 0 third = 0) :
    polynomial = 0 := by
  have primitive_eq := binaryShearInvariant_homogeneous primitive binary shear
  rw [primitive_eq] at coordinate
  have scalar_zero : polynomialValue primitive.val 0 1 0 = 0 := by
    have value := boundary 0 1
    rw [coordinate] at value
    simp [polynomialValue, zero_pow (Nat.ne_zero_of_lt degree_positive)] at value
    simpa only [polynomialValue] using value
  rw [coordinate, scalar_zero]
  simp

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
