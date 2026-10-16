module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialAntiderivative
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def ternaryInfinitesimalSubstitution (matrix : Matrix (Fin 3) (Fin 3) ℂ) : Module.End ℂ Poly where
  toFun polynomial := ∑ index, linearForm matrix index * pderiv index polynomial
  map_add' first second := by simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' scalar polynomial := by
    change (∑ index, linearForm matrix index * pderiv index (scalar • polynomial)) =
      scalar • (∑ index, linearForm matrix index * pderiv index polynomial)
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum]

theorem ternaryInfinitesimalSubstitution_C (matrix : Matrix (Fin 3) (Fin 3) ℂ) (scalar : ℂ) :
    ternaryInfinitesimalSubstitution matrix (C scalar) = 0 := by
  simp [ternaryInfinitesimalSubstitution]

theorem ternaryInfinitesimalSubstitution_mul_X (matrix : Matrix (Fin 3) (Fin 3) ℂ)
    (polynomial : Poly) (generator : Fin 3) :
    ternaryInfinitesimalSubstitution matrix (polynomial * X generator) =
      ternaryInfinitesimalSubstitution matrix polynomial * X generator + polynomial * linearForm matrix generator := by
  fin_cases generator <;>
    simp [ternaryInfinitesimalSubstitution, Fin.sum_univ_three, pderiv_X] <;> ring

theorem ternary_linearForm_coeff_hasDerivAt
    (matrices : ℝ → Matrix (Fin 3) (Fin 3) ℂ) (derivative : Matrix (Fin 3) (Fin 3) ℂ)
    (entries : ∀ row column, HasDerivAt (fun parameter => matrices parameter row column)
      (derivative row column) 0) (row : Fin 3) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter => (linearForm (matrices parameter) row).coeff monomial)
      ((linearForm derivative row).coeff monomial) 0 := by
  simp only [linearForm, coeff_sum, coeff_C_mul]
  convert HasDerivAt.sum (u := Finset.univ)
    (fun column _ => (entries row column).mul_const ((X column).coeff monomial)) using 1; rfl

theorem ternary_substitute_coeff_hasDerivAt
    (matrices : ℝ → Matrix (Fin 3) (Fin 3) ℂ) (derivative : Matrix (Fin 3) (Fin 3) ℂ)
    (at_zero : matrices 0 = 1)
    (entries : ∀ row column, HasDerivAt (fun parameter => matrices parameter row column)
      (derivative row column) 0) (polynomial : Poly) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt (fun parameter => (substitute (matrices parameter) polynomial).coeff monomial)
      ((ternaryInfinitesimalSubstitution derivative polynomial).coeff monomial) 0 := by
  classical
  induction polynomial using MvPolynomial.induction_on generalizing monomial with
  | C scalar =>
    simpa only [substitute, bind₁_C_right, ternaryInfinitesimalSubstitution_C, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      (hasDerivAt_const (0 : ℝ) ((C scalar).coeff monomial))
  | add first second first_derivative second_derivative =>
    have derived := (first_derivative monomial).add (second_derivative monomial)
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    convert derived using 1
  | mul_X polynomial generator polynomial_derivative =>
    have derivative_sum := HasDerivAt.sum (u := Finset.antidiagonal monomial)
      (fun indices _ => (polynomial_derivative indices.1).mul
        (ternary_linearForm_coeff_hasDerivAt matrices derivative entries generator indices.2))
    have linear_one : linearForm (1 : Matrix (Fin 3) (Fin 3) ℂ) generator = X generator := by
      simp [linearForm, Matrix.one_apply]
    simp only [map_mul, substitute_X, coeff_mul, ternaryInfinitesimalSubstitution_mul_X, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    simp only [at_zero, substitute_one, AlgHom.id_apply, linear_one,
      Finset.sum_add_distrib] at derivative_sum
    convert derivative_sum using 1; first
      | (funext parameter; simp only [Finset.sum_apply, Pi.mul_apply])

theorem ternary_homogeneousAction_coeff_hasDerivAt {degree : ℕ}
    (matrices : ℝ → GL3) (derivative : Matrix (Fin 3) (Fin 3) ℂ)
    (at_zero : matrices 0 = 1)
    (determinant : ∀ parameter, (GeneralLinearGroup.det (matrices parameter)).val = 1)
    (inverse_entries : ∀ row column, HasDerivAt (fun parameter => (matrices parameter)⁻¹.val row column)
      (derivative row column) 0)
    (polynomial : HomogeneousPoly degree) (monomial : Fin 3 →₀ ℕ) :
    HasDerivAt
      (fun parameter => (homogeneousAction degree (-1) (matrices parameter) polynomial).val.coeff monomial)
      ((ternaryInfinitesimalSubstitution derivative polynomial.val).coeff monomial) 0 := by
  have matrix_zero : (matrices 0)⁻¹.val = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [at_zero, inv_one, GeneralLinearGroup.coe_one]
  have derived := ternary_substitute_coeff_hasDerivAt (fun parameter => (matrices parameter)⁻¹.val)
    derivative matrix_zero inverse_entries polynomial.val monomial
  apply derived.congr_of_eventuallyEq
  filter_upwards [] with parameter
  simp only [homogeneousAction_coe, action_apply, determinantCharacter,
    MonoidHom.coe_mk, OneHom.coe_mk, determinant parameter, one_zpow, one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
