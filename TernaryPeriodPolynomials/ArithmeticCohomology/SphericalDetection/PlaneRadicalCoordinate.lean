module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialRestriction

@[expose] public section


open GeneralEisenstein MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem homogeneous_binary_remainder {degree : ℕ} (polynomial : HomogeneousPoly (degree + 1)) :
    ∃ (binary : Binary.HomogeneousPoly (degree + 1)) (quotient : HomogeneousPoly degree),
      polynomial.val = binaryPolynomialLift binary.val + X 2 * quotient.val := by
  let binary : Binary.HomogeneousPoly (degree + 1) :=
    ⟨binaryPolynomialRestrict polynomial.val, binaryPolynomialRestrict_homogeneous polynomial.val polynomial.property⟩
  obtain ⟨quotient, equation⟩ := binaryPolynomialRestrict_difference_dvd polynomial.val
  have difference_degree : (polynomial.val - binaryPolynomialLift binary.val).IsHomogeneous (degree + 1) :=
    polynomial.property.sub binary.property.rename_isHomogeneous
  have quotient_degree : quotient.IsHomogeneous degree := by
    have homogeneous : (X 2 * quotient).IsHomogeneous (degree + 1) := by
      rw [← equation]
      exact difference_degree
    simpa only [Nat.add_sub_cancel] using homogeneous_of_X_mul 2 quotient homogeneous
  refine ⟨binary, ⟨quotient, quotient_degree⟩, ?_⟩
  change polynomial.val = binaryPolynomialLift (binaryPolynomialRestrict polynomial.val) + X 2 * quotient
  rw [← equation]
  ring

/-- Every closed plane-radical pair is a binary gradient plus a homogeneous boundary. -/
theorem planeRadical_normal_form {degree : ℕ} (alpha beta : HomogeneousPoly degree)
    (closed : X 2 * pderiv 0 beta.val = X 2 * pderiv 1 alpha.val) :
    ∃ (binary : Binary.HomogeneousPoly (degree + 1)) (potential : HomogeneousPoly degree),
      alpha.val = pderiv 0 (binaryPolynomialLift binary.val) + X 2 * pderiv 0 potential.val ∧
      beta.val = pderiv 1 (binaryPolynomialLift binary.val) + X 2 * pderiv 1 potential.val := by
  have derivatives : pderiv (0 : Fin 3) beta.val = pderiv 1 alpha.val :=
    mul_left_cancel₀ (X_ne_zero (2 : Fin 3)) closed
  obtain ⟨primitive, primitive_degree, alpha_eq, beta_eq⟩ := homogeneous_closed_pair_has_potential
    (0 : Fin 3) 1 (by decide) alpha.val beta.val alpha.property beta.property derivatives
  obtain ⟨binary, potential, equation⟩ := homogeneous_binary_remainder ⟨primitive, primitive_degree⟩
  dsimp only at equation
  refine ⟨binary, potential, ?_, ?_⟩
  · rw [← alpha_eq, equation, map_add, pderiv_mul]
    simp only [pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), zero_mul, zero_add]
  · rw [← beta_eq, equation, map_add, pderiv_mul]
    simp only [pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1), zero_mul, zero_add]

theorem binaryPolynomialRestrict_plane_normal (index : Fin 2) (binary : Binary.Poly) (potential : Poly) :
    binaryPolynomialRestrict
      (pderiv index.castSucc (binaryPolynomialLift binary) + X 2 * pderiv index.castSucc potential) =
      pderiv index binary := by
  rw [map_add, map_mul, binaryPolynomialRestrict_X]
  change binaryPolynomialRestrict (pderiv index.castSucc (binaryPolynomialLift binary)) +
    0 * binaryPolynomialRestrict (pderiv index.castSucc potential) = pderiv index binary
  rw [zero_mul, add_zero]
  rw [← binaryPolynomialRestrict_pderiv, binaryPolynomialRestrict_lift]

theorem binaryPolynomialRestrict_plane_first (binary : Binary.Poly) (potential : Poly) :
    binaryPolynomialRestrict (pderiv 0 (binaryPolynomialLift binary) + X 2 * pderiv 0 potential) =
      pderiv 0 binary := binaryPolynomialRestrict_plane_normal (0 : Fin 2) binary potential

theorem binaryPolynomialRestrict_plane_second (binary : Binary.Poly) (potential : Poly) :
    binaryPolynomialRestrict (pderiv 1 (binaryPolynomialLift binary) + X 2 * pderiv 1 potential) =
      pderiv 1 binary := binaryPolynomialRestrict_plane_normal (1 : Fin 2) binary potential

theorem binaryHomogeneous_pderivs_zero {degree : ℕ} (binary : Binary.HomogeneousPoly (degree + 1))
    (first_zero : pderiv (0 : Fin 2) binary.val = 0) (second_zero : pderiv (1 : Fin 2) binary.val = 0) :
    binary = 0 := by
  have euler := binary.property.sum_X_mul_pderiv
  rw [Fin.sum_univ_two, first_zero, second_zero, mul_zero, mul_zero, add_zero,
    ← Nat.cast_smul_eq_nsmul ℂ] at euler
  have nonzero : ((degree + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero degree)
  apply Subtype.ext
  exact (smul_eq_zero.mp euler.symm).resolve_left nonzero

theorem binaryHomogeneous_pderivs_injective {degree : ℕ}
    (first second : Binary.HomogeneousPoly (degree + 1))
    (first_derivative : pderiv (0 : Fin 2) first.val = pderiv 0 second.val)
    (second_derivative : pderiv (1 : Fin 2) first.val = pderiv 1 second.val) : first = second := by
  apply sub_eq_zero.mp
  apply binaryHomogeneous_pderivs_zero
  · change pderiv (0 : Fin 2) (first.val - second.val) = 0
    rw [map_sub, first_derivative, sub_self]
  · change pderiv (1 : Fin 2) (first.val - second.val) = 0
    rw [map_sub, second_derivative, sub_self]

/-- The binary term of a plane-radical normal form vanishes exactly on homogeneous boundaries. -/
theorem planeRadical_normal_form_zero_iff {degree : ℕ} (alpha beta : HomogeneousPoly degree)
    (binary : Binary.HomogeneousPoly (degree + 1)) (potential : HomogeneousPoly degree)
    (alpha_eq : alpha.val = pderiv 0 (binaryPolynomialLift binary.val) + X 2 * pderiv 0 potential.val)
    (beta_eq : beta.val = pderiv 1 (binaryPolynomialLift binary.val) + X 2 * pderiv 1 potential.val) :
    binary = 0 ↔ ∃ boundary : HomogeneousPoly degree,
      alpha.val = X 2 * pderiv 0 boundary.val ∧ beta.val = X 2 * pderiv 1 boundary.val := by
  constructor
  · intro zero
    refine ⟨potential, ?_, ?_⟩
    · simpa only [zero, Submodule.coe_zero, map_zero, zero_add] using alpha_eq
    · simpa only [zero, Submodule.coe_zero, map_zero, zero_add] using beta_eq
  · rintro ⟨boundary, first_eq, second_eq⟩
    apply binaryHomogeneous_pderivs_zero
    · have equation := congrArg binaryPolynomialRestrict (alpha_eq.symm.trans first_eq)
      rw [binaryPolynomialRestrict_plane_first, map_mul, binaryPolynomialRestrict_X] at equation
      simpa using equation
    · have equation := congrArg binaryPolynomialRestrict (beta_eq.symm.trans second_eq)
      rw [binaryPolynomialRestrict_plane_second, map_mul, binaryPolynomialRestrict_X] at equation
      simpa using equation

theorem planeRadical_normal_form_unique {degree : ℕ}
    (first second : Binary.HomogeneousPoly (degree + 1)) (first_potential second_potential : Poly)
    (first_eq : pderiv 0 (binaryPolynomialLift first.val) + X 2 * pderiv 0 first_potential =
      pderiv 0 (binaryPolynomialLift second.val) + X 2 * pderiv 0 second_potential)
    (second_eq : pderiv 1 (binaryPolynomialLift first.val) + X 2 * pderiv 1 first_potential =
      pderiv 1 (binaryPolynomialLift second.val) + X 2 * pderiv 1 second_potential) : first = second := by
  apply binaryHomogeneous_pderivs_injective
  · have equation := congrArg binaryPolynomialRestrict first_eq
    rwa [binaryPolynomialRestrict_plane_first, binaryPolynomialRestrict_plane_first] at equation
  · have equation := congrArg binaryPolynomialRestrict second_eq
    rwa [binaryPolynomialRestrict_plane_second, binaryPolynomialRestrict_plane_second] at equation

end TernaryPeriodPolynomials.SphericalDetection.Helpers
