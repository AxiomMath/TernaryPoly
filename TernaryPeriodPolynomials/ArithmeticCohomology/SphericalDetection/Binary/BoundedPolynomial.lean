module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CentralAction
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem complex_polynomial_constant_of_nat_bound (polynomial : Polynomial ℂ) (bound : ℝ)
    (bounded : ∀ number : ℕ, ‖polynomial.eval (number : ℂ)‖ ≤ bound) :
    polynomial = Polynomial.C (polynomial.eval 0) := by
  have degree_zero : polynomial.degree ≤ 0 := by
    by_contra nonconstant
    have unbounded_arguments : Tendsto (fun number : ℕ => ‖(number : ℂ)‖) atTop atTop := by
      simpa only [norm_natCast] using
        (tendsto_natCast_atTop_atTop : Tendsto (fun number : ℕ => (number : ℝ)) atTop atTop)
    have unbounded_values := polynomial.tendsto_norm_atTop (lt_of_not_ge nonconstant) unbounded_arguments
    obtain ⟨number, greater⟩ := (unbounded_values.eventually_gt_atTop bound).exists
    exact (not_lt_of_ge (bounded number)) greater
  have constant := Polynomial.eq_C_of_degree_le_zero degree_zero
  conv_rhs => rw [constant, Polynomial.eval_C]
  exact constant

def binaryAffinePolynomial (polynomial : Binary.Poly) (substitutions : Fin 2 → Polynomial ℂ) : Polynomial ℂ :=
  eval₂Hom Polynomial.C substitutions polynomial

theorem binaryAffinePolynomial_eval (polynomial : Binary.Poly)
    (substitutions : Fin 2 → Polynomial ℂ) (value : ℂ) :
    Polynomial.eval value (binaryAffinePolynomial polynomial substitutions) =
      eval (fun position => Polynomial.eval value (substitutions position)) polynomial := by
  have constants : (Polynomial.evalRingHom value).comp Polynomial.C = RingHom.id ℂ := by
    ext scalar
    exact Polynomial.eval_C
  change (Polynomial.evalRingHom value) ((eval₂Hom Polynomial.C substitutions) polynomial) = _
  rw [map_eval₂Hom, constants]
  rfl

theorem homogeneous_eval_scalar {degree : ℕ} (polynomial : Binary.Poly)
    (homogeneous : polynomial.IsHomogeneous degree) (scalar : ℂ) (values : Fin 2 → ℂ) :
    eval (fun position => scalar * values position) polynomial =
      scalar ^ degree * eval values polynomial := by
  have scaling := congrArg (eval values)
    (homogeneous_scalar_substitution polynomial homogeneous scalar)
  have constants : (eval values).comp C = RingHom.id ℂ := eval₂Hom_comp_C _ _
  simp only [aeval_eq_eval₂Hom, map_eval₂Hom, constants, eval_C, eval_X,
    Algebra.smul_def, map_mul, MvPolynomial.algebraMap_eq] at scaling
  exact scaling

theorem binaryAffinePolynomial_pair_eval (polynomial : Binary.Poly)
    (first second : Polynomial ℂ) (value : ℂ) :
    Polynomial.eval value (binaryAffinePolynomial polynomial ![first, second]) =
      eval ![Polynomial.eval value first, Polynomial.eval value second] polynomial := by
  rw [binaryAffinePolynomial_eval]
  apply congrArg (fun values : Fin 2 → ℂ => eval values polynomial)
  funext position
  fin_cases position <;> rfl

theorem homogeneous_binary_eq_zero_of_affine_bounds {degree : ℕ} (positive : 0 < degree)
    (polynomial : Binary.Poly) (homogeneous : polynomial.IsHomogeneous degree)
    (first_bound second_bound : ℝ)
    (first_bounded : ∀ number : ℕ, ‖eval ![(number : ℂ), 1] polynomial‖ ≤ first_bound)
    (second_bounded : ∀ number : ℕ, ‖eval ![1, (number : ℂ)] polynomial‖ ≤ second_bound) :
    polynomial = 0 := by
  have first_polynomial := complex_polynomial_constant_of_nat_bound
    (binaryAffinePolynomial polynomial ![Polynomial.X, 1]) first_bound (by
      intro number
      simpa only [binaryAffinePolynomial_pair_eval, Polynomial.eval_X, Polynomial.eval_one] using
        first_bounded number)
  have second_polynomial := complex_polynomial_constant_of_nat_bound
    (binaryAffinePolynomial polynomial ![1, Polynomial.X]) second_bound (by
      intro number
      simpa only [binaryAffinePolynomial_pair_eval, Polynomial.eval_X, Polynomial.eval_one] using
        second_bounded number)
  have first (value : ℂ) : eval ![value, 1] polynomial = eval ![0, 1] polynomial := by
    have equality := congrArg (Polynomial.eval value) first_polynomial
    simpa only [Polynomial.eval_C, binaryAffinePolynomial_pair_eval, Polynomial.eval_X,
      Polynomial.eval_one] using equality
  have second (value : ℂ) : eval ![1, value] polynomial = eval ![1, 0] polynomial := by
    have equality := congrArg (Polynomial.eval value) second_polynomial
    simpa only [Polynomial.eval_C, binaryAffinePolynomial_pair_eval, Polynomial.eval_X,
      Polynomial.eval_one] using equality
  have second_first (value : ℂ) : eval ![1, value] polynomial = eval ![0, 1] polynomial :=
    (second value).trans ((second 1).symm.trans (first 1))
  have constant_zero : eval ![0, 1] polynomial = 0 := by
    have scaling := homogeneous_eval_scalar polynomial homogeneous 2 ![(2 : ℂ)⁻¹, 1]
    have points : (fun position : Fin 2 => (2 : ℂ) * ![(2 : ℂ)⁻¹, 1] position) = ![1, 2] := by
      funext position
      fin_cases position <;> norm_num
    rw [points, second_first, first (2 : ℂ)⁻¹] at scaling
    have power_ne : (2 : ℂ) ^ degree ≠ 1 := by
      exact_mod_cast (ne_of_gt (Nat.one_lt_two_pow_iff.mpr (Nat.ne_of_gt positive)))
    have product : ((2 : ℂ) ^ degree - 1) * eval ![0, 1] polynomial = 0 := by
      rw [sub_mul, one_mul, ← scaling, sub_self]
    exact (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr power_ne)
  apply homogeneous.eq_zero_of_forall_eval_eq_zero
  intro values
  by_cases last_zero : values 1 = 0
  · have scaling := homogeneous_eval_scalar polynomial homogeneous (values 0) ![1, 0]
    have points : (fun position : Fin 2 => values 0 * ![1, 0] position) = values := by
      funext position
      fin_cases position <;> simp [last_zero]
    rw [points, second_first, constant_zero, mul_zero] at scaling
    exact scaling
  · have scaling := homogeneous_eval_scalar polynomial homogeneous (values 1) ![values 0 / values 1, 1]
    have points : (fun position : Fin 2 => values 1 * ![values 0 / values 1, 1] position) = values := by
      funext position
      fin_cases position
      · change values 1 * (values 0 / values 1) = values 0
        field_simp
      · simp
    rw [points, first, constant_zero, mul_zero] at scaling
    exact scaling

end TernaryPeriodPolynomials.SphericalDetection.Helpers
