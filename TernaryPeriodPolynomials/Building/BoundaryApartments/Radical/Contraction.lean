module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Taylor
public import TernaryPeriodPolynomials.Building.BoundaryApartments.DetectionAlgebra
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix MvPolynomial

def radicalTranslation (degree : ℕ) (index : Fin 3) (polynomial : HomogeneousPoly degree) :
    HomogeneousPoly degree :=
  ⟨bind₁ ![X 0 - X index, X 1, X 2] polynomial.val,
    bind_homogeneous polynomial.property ![X 0 - X index, X 1, X 2] (by
      intro current
      fin_cases current
      · exact (isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ index)
      · exact isHomogeneous_X ℂ 1
      · exact isHomogeneous_X ℂ 2)⟩

theorem exponentialRadical_aeval (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : HomogeneousPoly degree) :
    (Polynomial.aeval (radicalDerivative degree index)
      (PowerSeries.trunc (degree + 1) (PowerSeries.exp ℚ))) polynomial =
        radicalTranslation degree index polynomial := by
  apply Subtype.ext
  rw [aeval_trunc_apply_val degree (degree + 1) index index_nonzero]
  apply MvPolynomial.funext
  intro coordinates
  have coordinates_eta : coordinates = ![coordinates 0, coordinates 1, coordinates 2] := by
    funext current
    fin_cases current <;> rfl
  have coefficients (iterations : ℕ) :
      ((PowerSeries.coeff iterations (PowerSeries.exp ℚ) : ℚ) : ℂ) =
        (iterations.factorial : ℂ)⁻¹ := by
    simp [PowerSeries.coeff_exp]
  simp only [map_sum, map_mul, map_pow, map_neg, eval_C, eval_X, coefficients]
  rw [coordinates_eta]
  change _ = polynomialValue (bind₁ ![X 0 - X index, X 1, X 2] polynomial.val)
    (coordinates 0) (coordinates 1) (coordinates 2)
  rw [polynomialValue_bind]
  have substituted :
      (fun current => polynomialValue (![X 0 - X index, X 1, X 2] current)
        (coordinates 0) (coordinates 1) (coordinates 2)) =
          ![coordinates 0 - coordinates index, coordinates 1, coordinates 2] := by
    funext current
    fin_cases current <;> simp [polynomialValue, ← coordinates_eta]
  rw [substituted]
  have expansion := radicalTaylor_eval polynomial
    (coordinates 0) (coordinates 1) (coordinates 2) (-coordinates index)
  simp only [polynomialValue] at expansion
  simp only [sub_eq_add_neg] at *
  rw [expansion]
  apply Finset.sum_congr rfl
  intro iterations _
  rw [← coordinates_eta]

theorem bernoulliRadical_difference (degree : ℕ) (index : Fin 3) (index_nonzero : index ≠ 0)
    (polynomial : HomogeneousPoly degree) :
    bernoulliOperator degree (X index)
      ((radicalTranslation degree index polynomial).val - polynomial.val) =
        -X index * pderiv 0 polynomial.val := by
  have nilpotent : radicalDerivative degree index ^ (degree + 2) = 0 := by
    rw [show degree + 2 = (degree + 1) + 1 from rfl, pow_succ,
      radicalDerivative_nilpotent degree index index_nonzero, zero_mul]
  have identity := finiteBernoulli_mul_exp_sub_one (radicalDerivative degree index) degree nilpotent
  rw [aeval_trunc_degree_bound degree index index_nonzero,
    aeval_trunc_degree_bound degree index index_nonzero] at identity
  have evaluated := congrArg (fun operator : Module.End ℂ (HomogeneousPoly degree) =>
    (operator polynomial).val) identity
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    exponentialRadical_aeval degree index index_nonzero] at evaluated
  rw [bernoulliRadical_aeval degree index index_nonzero] at evaluated
  exact evaluated

theorem radicalContraction_coboundary (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    X 2 * bernoulliOperator degree (X 1)
      ((radicalTranslation degree 1 polynomial).val - polynomial.val) -
    X 1 * bernoulliOperator degree (X 2)
      ((radicalTranslation degree 2 polynomial).val - polynomial.val) = 0 := by
  rw [bernoulliRadical_difference degree 1 (by decide),
    bernoulliRadical_difference degree 2 (by decide)]
  ring

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
