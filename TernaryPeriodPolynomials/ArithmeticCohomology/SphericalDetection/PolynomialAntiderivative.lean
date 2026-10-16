module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def polynomialAntiderivative {σ : Type*} (coordinate : σ) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  (basisMonomials σ ℂ).constr ℂ (fun exponent =>
    monomial (exponent + Finsupp.single coordinate 1) ((exponent coordinate + 1 : ℂ)⁻¹))

theorem polynomialAntiderivative_monomial {σ : Type*} (coordinate : σ)
    (exponent : σ →₀ ℕ) (coefficient : ℂ) :
    polynomialAntiderivative coordinate (monomial exponent coefficient) =
      monomial (exponent + Finsupp.single coordinate 1) (coefficient / (exponent coordinate + 1 : ℂ)) := by
  have monomial_eq : monomial exponent coefficient = coefficient • basisMonomials σ ℂ exponent := by
    simp [coe_basisMonomials, smul_monomial]
  rw [monomial_eq, map_smul]
  change coefficient • ((basisMonomials σ ℂ).constr ℂ _) (basisMonomials σ ℂ exponent) = _
  rw [Module.Basis.constr_basis, smul_monomial]
  rfl

theorem pderiv_polynomialAntiderivative {σ : Type*} (coordinate : σ) (polynomial : MvPolynomial σ ℂ) :
    pderiv coordinate (polynomialAntiderivative coordinate polynomial) = polynomial := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | monomial exponent coefficient =>
    rw [polynomialAntiderivative_monomial, pderiv_monomial]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one,
      add_tsub_cancel_right]
    have nonzero : (exponent coordinate + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (exponent coordinate)
    rw [div_mul_cancel₀ _ nonzero]
  | add first second first_proof second_proof =>
    rw [map_add, map_add, first_proof, second_proof]

theorem pderiv_commute {σ : Type*} (first second : σ) (polynomial : MvPolynomial σ ℂ) :
    pderiv first (pderiv second polynomial) = pderiv second (pderiv first polynomial) := by
  classical
  by_cases same : first = second
  · rw [same]
  · ext exponent
    simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_eq_of_ne same,
      Finsupp.single_eq_of_ne (Ne.symm same), add_zero]
    rw [add_right_comm exponent (Finsupp.single first 1) (Finsupp.single second 1)]
    ring

theorem pderiv_polynomialAntiderivative_commute {σ : Type*} (first second : σ)
    (distinct : first ≠ second) (polynomial : MvPolynomial σ ℂ) :
    pderiv first (polynomialAntiderivative second polynomial) =
      polynomialAntiderivative second (pderiv first polynomial) := by
  classical
  induction polynomial using MvPolynomial.induction_on' with
  | monomial exponent coefficient =>
    rw [polynomialAntiderivative_monomial, pderiv_monomial, pderiv_monomial,
      polynomialAntiderivative_monomial]
    have exponent_eq : (exponent + Finsupp.single second 1) - Finsupp.single first 1 =
        (exponent - Finsupp.single first 1) + Finsupp.single second 1 := by
      ext index
      by_cases first_index : index = first <;> by_cases second_index : index = second <;>
        simp_all [Finsupp.tsub_apply, Finsupp.add_apply]
    rw [exponent_eq]
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne distinct,
      Finsupp.single_eq_of_ne (Ne.symm distinct), add_zero, tsub_zero]
    congr 1
    ring
  | add first_polynomial second_polynomial first_proof second_proof =>
    rw [map_add, map_add, map_add, map_add, first_proof, second_proof]

/-- A closed polynomial one-form in two distinct coordinates has an explicit polynomial potential. -/
theorem polynomial_closed_pair_has_potential {σ : Type*} (first second : σ)
    (distinct : first ≠ second) (alpha beta : MvPolynomial σ ℂ)
    (closed : pderiv first beta = pderiv second alpha) :
    ∃ potential : MvPolynomial σ ℂ,
      pderiv first potential = alpha ∧ pderiv second potential = beta := by
  let initial := polynomialAntiderivative first alpha
  let residual := beta - pderiv second initial
  have residual_closed : pderiv first residual = 0 := by
    dsimp only [residual, initial]
    rw [map_sub, pderiv_commute first second, pderiv_polynomialAntiderivative, closed, sub_self]
  refine ⟨initial + polynomialAntiderivative second residual, ?_, ?_⟩
  · rw [map_add, pderiv_polynomialAntiderivative_commute first second distinct,
      residual_closed, map_zero, add_zero]
    exact pderiv_polynomialAntiderivative first alpha
  · rw [map_add, pderiv_polynomialAntiderivative]
    dsimp only [residual]
    abel

theorem polynomialAntiderivative_homogeneous {σ : Type*} (coordinate : σ)
    (polynomial : MvPolynomial σ ℂ) {degree : ℕ} (homogeneous : polynomial.IsHomogeneous degree) :
    (polynomialAntiderivative coordinate polynomial).IsHomogeneous (degree + 1) := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff polynomial]
  rw [map_sum]
  apply IsHomogeneous.sum
  intro exponent member
  rw [polynomialAntiderivative_monomial]
  apply isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single]
  congr 1
  rw [Finsupp.degree_eq_weight_one]
  exact homogeneous (mem_support_iff.mp member)

theorem homogeneous_closed_pair_has_potential {σ : Type*} (first second : σ)
    (distinct : first ≠ second) (alpha beta : MvPolynomial σ ℂ) {degree : ℕ}
    (alpha_degree : alpha.IsHomogeneous degree) (beta_degree : beta.IsHomogeneous degree)
    (closed : pderiv first beta = pderiv second alpha) :
    ∃ potential : MvPolynomial σ ℂ, potential.IsHomogeneous (degree + 1) ∧
      pderiv first potential = alpha ∧ pderiv second potential = beta := by
  let initial := polynomialAntiderivative first alpha
  let residual := beta - pderiv second initial
  have initial_degree : initial.IsHomogeneous (degree + 1) :=
    polynomialAntiderivative_homogeneous first alpha alpha_degree
  have residual_degree : residual.IsHomogeneous degree :=
    beta_degree.sub (by simpa using MvPolynomial.IsHomogeneous.pderiv (i := second) initial_degree)
  have residual_closed : pderiv first residual = 0 := by
    dsimp only [residual, initial]
    rw [map_sub, pderiv_commute first second, pderiv_polynomialAntiderivative, closed, sub_self]
  refine ⟨initial + polynomialAntiderivative second residual,
    initial_degree.add (polynomialAntiderivative_homogeneous second residual residual_degree), ?_, ?_⟩
  · rw [map_add, pderiv_polynomialAntiderivative_commute first second distinct,
      residual_closed, map_zero, add_zero]
    exact pderiv_polynomialAntiderivative first alpha
  · rw [map_add, pderiv_polynomialAntiderivative]
    dsimp only [residual]
    abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
