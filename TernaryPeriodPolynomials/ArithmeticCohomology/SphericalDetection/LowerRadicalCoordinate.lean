module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PolynomialDerivativeKernel
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def lowerRadicalContraction (alpha beta : Poly) : Poly := X 1 * alpha - X 0 * beta

theorem lowerRadicalContraction_homogeneous {degree : ℕ} (alpha beta : Poly)
    (alpha_degree : alpha.IsHomogeneous degree) (beta_degree : beta.IsHomogeneous degree) :
    (lowerRadicalContraction alpha beta).IsHomogeneous (degree + 1) := by
  have homogeneous := ((isHomogeneous_X ℂ (1 : Fin 3)).mul alpha_degree).sub
    ((isHomogeneous_X ℂ (0 : Fin 3)).mul beta_degree)
  change (X 1 * alpha - X 0 * beta).IsHomogeneous (degree + 1)
  simpa only [Nat.add_comm] using homogeneous

theorem lowerRadicalContraction_pderiv_third (alpha beta : Poly)
    (closed : X 0 * pderiv 2 beta = X 1 * pderiv 2 alpha) :
    pderiv (2 : Fin 3) (lowerRadicalContraction alpha beta) = 0 := by
  simp only [lowerRadicalContraction, map_sub, pderiv_mul,
    pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2), zero_mul, zero_add]
  exact sub_eq_zero.mpr closed.symm

theorem lowerRadicalContraction_exists_binary {degree : ℕ} (alpha beta : HomogeneousPoly degree)
    (closed : X 0 * pderiv 2 beta.val = X 1 * pderiv 2 alpha.val) :
    ∃ binary : Binary.HomogeneousPoly (degree + 1),
      (binaryHomogeneousLift (degree + 1) binary).val = lowerRadicalContraction alpha.val beta.val := by
  obtain ⟨binary, equality⟩ := homogeneous_pderiv_third_zero_exists_binary
    ⟨lowerRadicalContraction alpha.val beta.val,
      lowerRadicalContraction_homogeneous alpha.val beta.val alpha.property beta.property⟩
    (lowerRadicalContraction_pderiv_third alpha.val beta.val closed)
  exact ⟨binary, congrArg Subtype.val equality⟩

theorem lowerRadicalContraction_boundary (potential : Poly) :
    lowerRadicalContraction (X 0 * pderiv 2 potential) (X 1 * pderiv 2 potential) = 0 := by
  unfold lowerRadicalContraction
  ring

/-- The contraction kills exactly the infinitesimal lower-radical boundaries in positive degree. -/
theorem lowerRadicalContraction_eq_zero_iff {degree : ℕ} (positive : 0 < degree)
    (alpha beta : HomogeneousPoly degree) :
    lowerRadicalContraction alpha.val beta.val = 0 ↔
      ∃ potential : HomogeneousPoly degree,
        alpha.val = X 0 * pderiv 2 potential.val ∧ beta.val = X 1 * pderiv 2 potential.val := by
  constructor
  · intro zero
    have equality : X 1 * alpha.val = X 0 * beta.val := sub_eq_zero.mp zero
    have divides : (X (0 : Fin 3) : Poly) ∣ X 1 * alpha.val := ⟨beta.val, equality⟩
    have not_divides : ¬ (X (0 : Fin 3) : Poly) ∣ X 1 := by
      rw [X_dvd_X]
      decide
    obtain ⟨factor, alpha_eq⟩ := (X_dvd_mul_iff.mp divides).resolve_left not_divides
    have beta_eq : beta.val = X 1 * factor := by
      apply mul_left_cancel₀ (X_ne_zero (0 : Fin 3))
      rw [← equality, alpha_eq]
      ring
    have factor_degree : factor.IsHomogeneous (degree - 1) :=
      homogeneous_of_X_mul 0 factor (by rw [← alpha_eq]; exact alpha.property)
    have potential_degree : (polynomialAntiderivative (2 : Fin 3) factor).IsHomogeneous degree := by
      have degree_eq : degree - 1 + 1 = degree := by omega
      simpa only [degree_eq] using polynomialAntiderivative_homogeneous 2 factor factor_degree
    refine ⟨⟨polynomialAntiderivative 2 factor, potential_degree⟩, ?_, ?_⟩
    · rw [pderiv_polynomialAntiderivative]
      exact alpha_eq
    · rw [pderiv_polynomialAntiderivative]
      exact beta_eq
  · rintro ⟨potential, alpha_eq, beta_eq⟩
    rw [alpha_eq, beta_eq]
    exact lowerRadicalContraction_boundary potential.val

/-- Every binary homogeneous polynomial occurs as a closed lower-radical contraction. -/
theorem lowerRadicalContraction_surjective {degree : ℕ}
    (binary : Binary.HomogeneousPoly (degree + 1)) :
    ∃ alpha beta : HomogeneousPoly degree,
      X 0 * pderiv 2 beta.val = X 1 * pderiv 2 alpha.val ∧
      lowerRadicalContraction alpha.val beta.val =
        (binaryHomogeneousLift (degree + 1) binary).val := by
  let polynomial := (binaryHomogeneousLift (degree + 1) binary).val
  let scalar : ℂ := (degree + 1 : ℂ)⁻¹
  have homogeneous : polynomial.IsHomogeneous (degree + 1) :=
    (binaryHomogeneousLift (degree + 1) binary).property
  have independent : pderiv (2 : Fin 3) polynomial = 0 := binaryPolynomialLift_pderiv_third binary.val
  have alpha_degree : (scalar • pderiv (1 : Fin 3) polynomial).IsHomogeneous degree := by
    rw [Algebra.smul_def]
    have derivative_degree : (pderiv (1 : Fin 3) polynomial).IsHomogeneous degree := by
      simpa using homogeneous.pderiv (i := (1 : Fin 3))
    exact derivative_degree.C_mul scalar
  have beta_degree : (-(scalar • pderiv (0 : Fin 3) polynomial)).IsHomogeneous degree := by
    apply IsHomogeneous.neg
    rw [Algebra.smul_def]
    have derivative_degree : (pderiv (0 : Fin 3) polynomial).IsHomogeneous degree := by
      simpa using homogeneous.pderiv (i := (0 : Fin 3))
    exact derivative_degree.C_mul scalar
  refine ⟨⟨scalar • pderiv 1 polynomial, alpha_degree⟩,
    ⟨-(scalar • pderiv 0 polynomial), beta_degree⟩, ?_, ?_⟩
  · change X 0 * pderiv 2 (-(scalar • pderiv 0 polynomial)) = X 1 * pderiv 2 (scalar • pderiv 1 polynomial)
    rw [map_neg, Derivation.map_smul, Derivation.map_smul, pderiv_commute 2 0, pderiv_commute 2 1,
      independent, map_zero, map_zero, smul_zero, neg_zero, mul_zero, mul_zero]
  · change lowerRadicalContraction (scalar • pderiv 1 polynomial) (-(scalar • pderiv 0 polynomial)) = polynomial
    have contraction : lowerRadicalContraction (scalar • pderiv 1 polynomial) (-(scalar • pderiv 0 polynomial)) =
        scalar • (X 0 * pderiv 0 polynomial + X 1 * pderiv 1 polynomial) := by
      simp only [lowerRadicalContraction, Algebra.smul_def]
      ring
    have euler := homogeneous.sum_X_mul_pderiv
    simp only [Fin.sum_univ_three, independent, mul_zero, add_zero] at euler
    rw [contraction, euler, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have nonzero : (degree + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
    dsimp only [scalar]
    rw [Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ nonzero, one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
