module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Coefficient.Infinitesimal
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.PolynomialDerivative

/-- The derivation induced by an infinitesimal change of the two variables. -/
noncomputable def variableDerivative (direction : Matrix (Fin 2) (Fin 2) ℂ) :
    Derivation ℂ Binary.Poly Binary.Poly :=
  MvPolynomial.mkDerivation ℂ (Binary.linearForm direction)

theorem linearForm_one (position : Fin 2) :
    Binary.linearForm (1 : Matrix (Fin 2) (Fin 2) ℂ) position = MvPolynomial.X position := by
  rw [← Binary.substitute_X, Binary.substitute_one]
  rfl

theorem coefficient_product (first second : ℝ → Binary.Poly) (firstDerivative secondDerivative : Binary.Poly)
    (point : ℝ)
    (firstRegular : ∀ monomial, HasDerivAt (fun parameter => (first parameter).coeff monomial)
      (firstDerivative.coeff monomial) point)
    (secondRegular : ∀ monomial, HasDerivAt (fun parameter => (second parameter).coeff monomial)
      (secondDerivative.coeff monomial) point)
    (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun parameter => (first parameter * second parameter).coeff monomial)
      ((firstDerivative * second point + first point * secondDerivative).coeff monomial) point := by
  classical
  simp only [MvPolynomial.coeff_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum (fun pair _ => (firstRegular pair.1).mul (secondRegular pair.2))

theorem linearForm_derivative (family : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (direction : Matrix (Fin 2) (Fin 2) ℂ) (point : ℝ)
    (regularity : ∀ row column, HasDerivAt (fun parameter => family parameter row column)
      (direction row column) point) (position : Fin 2) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun parameter => (Binary.linearForm (family parameter) position).coeff monomial)
      ((Binary.linearForm direction position).coeff monomial) point := by
  simp only [Binary.linearForm, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  exact HasDerivAt.fun_sum (fun other _ => (regularity position other).mul_const _)

/-- Coefficientwise chain rule, without imposing a topology on the full polynomial ring. -/
theorem substitute_derivative (family : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (direction : Matrix (Fin 2) (Fin 2) ℂ) (point : ℝ) (atPoint : family point = 1)
    (regularity : ∀ row column, HasDerivAt (fun parameter => family parameter row column)
      (direction row column) point) (polynomial : Binary.Poly) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun parameter => (Binary.substitute (family parameter) polynomial).coeff monomial)
      ((variableDerivative direction polynomial).coeff monomial) point := by
  induction polynomial using MvPolynomial.induction_on generalizing monomial with
  | C scalar =>
      simpa only [Binary.substitute, MvPolynomial.bind₁_C_right, variableDerivative,
        MvPolynomial.derivation_C, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
        hasDerivAt_const point ((MvPolynomial.C scalar).coeff monomial)
  | add first second firstInduction secondInduction =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      exact (firstInduction monomial).add (secondInduction monomial)
  | mul_X polynomial position inductionHypothesis =>
      have derivative := coefficient_product
        (fun parameter => Binary.substitute (family parameter) polynomial)
        (fun parameter => Binary.linearForm (family parameter) position)
        (variableDerivative direction polynomial) (Binary.linearForm direction position) point
        inductionHypothesis (linearForm_derivative family direction point regularity position) monomial
      simpa only [map_mul, Binary.substitute_X, Derivation.leibniz, variableDerivative,
        MvPolynomial.mkDerivation_X, atPoint, Binary.substitute_one, AlgHom.id_apply,
        linearForm_one, smul_eq_mul, mul_comm, add_comm] using derivative

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.PolynomialDerivative
