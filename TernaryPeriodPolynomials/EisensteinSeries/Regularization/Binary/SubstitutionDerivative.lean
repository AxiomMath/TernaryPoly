module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.PolynomialCasimir

@[expose] public section


open GeneralEisenstein MvPolynomial
open scoped BigOperators

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_linearForm_mul_coefficient
    (matrix : Matrix (Fin 2) (Fin 2) ℂ) (row : Fin 2)
    (polynomial : Binary.Poly) (monomial : Fin 2 →₀ ℕ) :
    (Binary.linearForm matrix row * polynomial).coeff monomial =
      ∑ column, matrix row column *
        if column ∈ monomial.support then polynomial.coeff (monomial - Finsupp.single column 1) else 0 := by
  classical
  simp only [Binary.linearForm, Finset.sum_mul, coeff_sum, mul_assoc, coeff_C_mul,
    coeff_X_mul']

theorem binary_linearForm_mul_hasDerivAt
    (matrix : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (tangent : Matrix (Fin 2) (Fin 2) ℂ)
    (family : ℝ → Binary.Poly) (velocity : Binary.Poly) (point : ℝ)
    (matrix_derivative : ∀ row column, HasDerivAt (fun t => matrix t row column) (tangent row column) point)
    (family_derivative : ∀ monomial, HasDerivAt (fun t => (family t).coeff monomial) (velocity.coeff monomial) point)
    (row : Fin 2) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t => (Binary.linearForm (matrix t) row * family t).coeff monomial)
      ((Binary.linearForm tangent row * family point +
        Binary.linearForm (matrix point) row * velocity).coeff monomial) point := by
  classical
  simp only [binary_linearForm_mul_coefficient, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ← Finset.sum_add_distrib]
  have term (column : Fin 2) :
      HasDerivAt
        (fun t => matrix t row column *
          if column ∈ monomial.support then (family t).coeff (monomial - Finsupp.single column 1) else 0)
        (tangent row column *
          (if column ∈ monomial.support then (family point).coeff (monomial - Finsupp.single column 1) else 0) +
          matrix point row column *
          (if column ∈ monomial.support then velocity.coeff (monomial - Finsupp.single column 1) else 0)) point := by
    split_ifs with member
    · exact (matrix_derivative row column).mul (family_derivative _)
    · simpa only [mul_zero, add_zero] using hasDerivAt_const point (0 : ℂ)
  convert! HasDerivAt.sum (fun column (_ : column ∈ Finset.univ) => term column) using 1

noncomputable def binarySubstitutionDifferential
    (matrix tangent : Matrix (Fin 2) (Fin 2) ℂ) (polynomial : Binary.Poly) : Binary.Poly :=
  ∑ row, Binary.linearForm tangent row * Binary.substitute matrix (pderiv row polynomial)

theorem binarySubstitutionDifferential_C
    (matrix tangent : Matrix (Fin 2) (Fin 2) ℂ) (scalar : ℂ) :
    binarySubstitutionDifferential matrix tangent (C scalar) = 0 := by
  simp [binarySubstitutionDifferential]

theorem binarySubstitutionDifferential_add
    (matrix tangent : Matrix (Fin 2) (Fin 2) ℂ) (first second : Binary.Poly) :
    binarySubstitutionDifferential matrix tangent (first + second) =
      binarySubstitutionDifferential matrix tangent first + binarySubstitutionDifferential matrix tangent second := by
  simp [binarySubstitutionDifferential, mul_add, Finset.sum_add_distrib]

theorem binarySubstitutionDifferential_mul_X
    (matrix tangent : Matrix (Fin 2) (Fin 2) ℂ) (polynomial : Binary.Poly) (column : Fin 2) :
    binarySubstitutionDifferential matrix tangent (polynomial * X column) =
      Binary.linearForm tangent column * Binary.substitute matrix polynomial +
        Binary.linearForm matrix column * binarySubstitutionDifferential matrix tangent polynomial := by
  classical
  fin_cases column <;>
    simp [binarySubstitutionDifferential, Fin.sum_univ_two, Binary.substitute_X,
      pderiv_X, Pi.single_apply] <;> ring

theorem binary_substitute_hasDerivAt
    (matrix : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (tangent : Matrix (Fin 2) (Fin 2) ℂ)
    (point : ℝ)
    (matrix_derivative : ∀ row column, HasDerivAt (fun t => matrix t row column) (tangent row column) point)
    (polynomial : Binary.Poly) (monomial : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t => (Binary.substitute (matrix t) polynomial).coeff monomial)
      ((binarySubstitutionDifferential (matrix point) tangent polynomial).coeff monomial) point := by
  induction polynomial using MvPolynomial.induction_on generalizing monomial with
  | C scalar =>
    simpa only [Binary.substitute, bind₁_C_right, binarySubstitutionDifferential_C, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      using hasDerivAt_const point ((C scalar).coeff monomial)
  | add first second first_derivative second_derivative =>
    convert! (first_derivative monomial).add (second_derivative monomial) using 1
    · ext t
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Pi.add_apply]
    · simp only [binarySubstitutionDifferential_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | mul_X polynomial column derivative =>
    simpa only [map_mul, Binary.substitute_X, binarySubstitutionDifferential_mul_X,
      mul_comm (Binary.substitute (matrix _) polynomial)]
      using binary_linearForm_mul_hasDerivAt matrix tangent
        (fun t => Binary.substitute (matrix t) polynomial)
        (binarySubstitutionDifferential (matrix point) tangent polynomial)
        point matrix_derivative derivative column monomial

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
