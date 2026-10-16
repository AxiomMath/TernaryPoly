module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Integration

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open MvPolynomial

def polynomialAntiderivative (polynomial : Poly) : Poly :=
  ∑ monomial ∈ polynomial.support,
    MvPolynomial.monomial (monomial + Finsupp.single 0 1)
      (polynomial.coeff monomial / ((monomial 0 : ℂ) + 1))

theorem polynomialAntiderivative_derivative (polynomial : Poly) :
    pderiv 0 (polynomialAntiderivative polynomial) = polynomial := by
  unfold polynomialAntiderivative
  rw [map_sum]
  have term (monomial : Fin 3 →₀ ℕ) :
      pderiv 0 (MvPolynomial.monomial (monomial + Finsupp.single 0 1)
        (polynomial.coeff monomial / ((monomial 0 : ℂ) + 1))) =
          MvPolynomial.monomial monomial (polynomial.coeff monomial) := by
    rw [pderiv_monomial, add_tsub_cancel_right]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
    have denominator_nonzero : (monomial 0 : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (monomial 0)
    rw [div_mul_cancel₀ _ denominator_nonzero]
  simp only [term]
  exact MvPolynomial.support_sum_monomial_coeff polynomial

theorem polynomialAntiderivative_homogeneous {degree : ℕ} {polynomial : Poly}
    (homogeneous : polynomial.IsHomogeneous degree) :
    (polynomialAntiderivative polynomial).IsHomogeneous (degree + 1) := by
  unfold polynomialAntiderivative
  apply IsHomogeneous.sum
  intro monomial monomial_mem
  apply isHomogeneous_monomial
  have monomial_degree : Finsupp.degree monomial = degree := by
    simpa only [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum,
      Pi.one_apply, smul_eq_mul, mul_one] using
        homogeneous (Finsupp.mem_support_iff.mp monomial_mem)
  rw [map_add, Finsupp.degree_single, monomial_degree]

theorem homogeneous_pderiv_surjective (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    ∃ primitive : HomogeneousPoly (degree + 1), pderiv 0 primitive.val = polynomial.val :=
  ⟨⟨polynomialAntiderivative polynomial.val, polynomialAntiderivative_homogeneous polynomial.property⟩,
    polynomialAntiderivative_derivative polynomial.val⟩

theorem homogeneous_of_X_mul {degree : ℕ} {index : Fin 3} {polynomial : Poly}
    (homogeneous : (X index * polynomial).IsHomogeneous (degree + 1)) :
    polynomial.IsHomogeneous degree := by
  intro monomial coefficient_nonzero
  have multiplied_nonzero : (X index * polynomial).coeff
      (Finsupp.single index 1 + monomial) ≠ 0 := by
    rw [coeff_X_mul]
    exact coefficient_nonzero
  have degree_eq := homogeneous multiplied_nonzero
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at degree_eq
  omega

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
