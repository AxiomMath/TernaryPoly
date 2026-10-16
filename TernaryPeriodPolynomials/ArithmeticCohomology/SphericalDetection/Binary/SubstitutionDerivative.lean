module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CoefficientRegularity
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryInfinitesimalSubstitution (matrix : Matrix (Fin 2) (Fin 2) ℂ) : Module.End ℂ Binary.Poly where
  toFun polynomial := ∑ position, Binary.linearForm matrix position * pderiv position polynomial
  map_add' first second := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' scalar polynomial := by
    change (∑ position, Binary.linearForm matrix position * pderiv position (scalar • polynomial)) =
      scalar • (∑ position, Binary.linearForm matrix position * pderiv position polynomial)
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum]

theorem binaryInfinitesimalSubstitution_C (matrix : Matrix (Fin 2) (Fin 2) ℂ) (scalar : ℂ) :
    binaryInfinitesimalSubstitution matrix (C scalar) = 0 := by
  simp [binaryInfinitesimalSubstitution]

theorem binaryInfinitesimalSubstitution_mul_X (matrix : Matrix (Fin 2) (Fin 2) ℂ)
    (polynomial : Binary.Poly) (generator : Fin 2) :
    binaryInfinitesimalSubstitution matrix (polynomial * X generator) =
      binaryInfinitesimalSubstitution matrix polynomial * X generator +
        polynomial * Binary.linearForm matrix generator := by
  fin_cases generator <;>
    simp [binaryInfinitesimalSubstitution, Fin.sum_univ_two, pderiv_X] <;> ring

theorem binaryInfinitesimalSubstitution_homogeneous (matrix : Matrix (Fin 2) (Fin 2) ℂ)
    {degree : ℕ} (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    (binaryInfinitesimalSubstitution matrix polynomial.val).IsHomogeneous (degree + 1) := by
  apply IsHomogeneous.sum
  intro position _
  convert (Binary.linearForm_homogeneous matrix position).mul
    (polynomial.property.pderiv (i := position)) using 1
  omega

def binaryInfinitesimalCoefficient (degree : ℕ) (matrix : Matrix (Fin 2) (Fin 2) ℂ) :
    Module.End ℂ (Binary.HomogeneousPoly (degree + 1)) where
  toFun polynomial := ⟨binaryInfinitesimalSubstitution matrix polynomial.val,
    binaryInfinitesimalSubstitution_homogeneous matrix polynomial⟩
  map_add' first second := Subtype.ext (map_add (binaryInfinitesimalSubstitution matrix) first.val second.val)
  map_smul' scalar polynomial := Subtype.ext (map_smul (binaryInfinitesimalSubstitution matrix) scalar polynomial.val)

theorem binary_linearForm_coeff_hasDerivAt
    (matrices : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (derivative : Matrix (Fin 2) (Fin 2) ℂ)
    (entries : ∀ row column, HasDerivAt (fun parameter => matrices parameter row column)
      (derivative row column) 0) (row : Fin 2) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun parameter => (Binary.linearForm (matrices parameter) row).coeff monomial)
      ((Binary.linearForm derivative row).coeff monomial) 0 := by
  simp only [Binary.linearForm, coeff_sum, coeff_C_mul]
  convert HasDerivAt.sum (u := Finset.univ)
    (fun column _ => (entries row column).mul_const ((X column).coeff monomial)) using 1; rfl

theorem binary_substitute_coeff_hasDerivAt
    (matrices : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (derivative : Matrix (Fin 2) (Fin 2) ℂ)
    (at_zero : matrices 0 = 1)
    (entries : ∀ row column, HasDerivAt (fun parameter => matrices parameter row column)
      (derivative row column) 0) (polynomial : Binary.Poly) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun parameter => (Binary.substitute (matrices parameter) polynomial).coeff monomial)
      ((binaryInfinitesimalSubstitution derivative polynomial).coeff monomial) 0 := by
  classical
  induction polynomial using MvPolynomial.induction_on generalizing monomial with
  | C scalar =>
    simpa only [Binary.substitute, bind₁_C_right, binaryInfinitesimalSubstitution_C, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      (hasDerivAt_const (0 : ℝ) ((C scalar).coeff monomial))
  | add first second first_derivative second_derivative =>
    have derived := (first_derivative monomial).add (second_derivative monomial)
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    convert derived using 1
  | mul_X polynomial generator polynomial_derivative =>
    have derivative_sum := HasDerivAt.sum (u := Finset.antidiagonal monomial)
      (fun indices _ => (polynomial_derivative indices.1).mul
        (binary_linearForm_coeff_hasDerivAt matrices derivative entries generator indices.2))
    have linear_one : Binary.linearForm (1 : Matrix (Fin 2) (Fin 2) ℂ) generator = X generator := by
      simp [Binary.linearForm, Matrix.one_apply]
    simp only [map_mul, Binary.substitute_X, coeff_mul, binaryInfinitesimalSubstitution_mul_X,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    simp only [at_zero, Binary.substitute_one, AlgHom.id_apply, linear_one,
      Finset.sum_add_distrib] at derivative_sum
    convert derivative_sum using 1; first
      | (funext parameter; simp only [Finset.sum_apply, Pi.mul_apply])

theorem binary_homogeneousAction_functional_hasDerivAt {degree : ℕ}
    (matrices : ℝ → Binary.GL2) (derivative : Matrix (Fin 2) (Fin 2) ℂ)
    (at_zero : matrices 0 = 1)
    (determinant : ∀ᶠ parameter in nhds (0 : ℝ), (GeneralLinearGroup.det (matrices parameter)).val = 1)
    (inverse_entries : ∀ row column, HasDerivAt (fun parameter => (matrices parameter)⁻¹.val row column)
      (derivative row column) 0)
    (polynomial : Binary.HomogeneousPoly (degree + 1))
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    HasDerivAt
      (fun parameter => functional (Binary.homogeneousAction (degree + 1) (-1) (matrices parameter) polynomial))
      (functional (binaryInfinitesimalCoefficient degree derivative polynomial)) 0 := by
  have spanned := binaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    rcases membership with ⟨monomial, rfl⟩
    have matrix_zero : (matrices 0)⁻¹.val = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [at_zero, inv_one, GeneralLinearGroup.coe_one]
    have derived := binary_substitute_coeff_hasDerivAt (fun parameter => (matrices parameter)⁻¹.val)
      derivative matrix_zero inverse_entries polynomial.val monomial
    apply derived.congr_of_eventuallyEq
    filter_upwards [determinant] with parameter determinant_one
    change (Binary.homogeneousAction (degree + 1) (-1) (matrices parameter) polynomial).val.coeff monomial = _
    simp only [Binary.homogeneousAction_coe, Binary.action_apply, Binary.determinantCharacter,
      MonoidHom.coe_mk, OneHom.coe_mk, determinant_one, one_zpow, one_smul]
  | zero => exact hasDerivAt_const (0 : ℝ) 0
  | add first second _ _ first_derivative second_derivative =>
    convert first_derivative.add second_derivative using 1
  | smul scalar functional _ derived =>
    convert derived.const_smul scalar using 1

end TernaryPeriodPolynomials.SphericalDetection.Helpers
