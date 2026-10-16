module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LeviConjugation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def planeRadicalCycles (degree : ℕ) : Submodule ℂ (Fin 2 → HomogeneousPoly degree) where
  carrier := {pair | X 2 * pderiv 0 (pair 1).val = X 2 * pderiv 1 (pair 0).val}
  zero_mem' := by simp
  add_mem' := by
    intro first second first_closed second_closed
    change X 2 * pderiv 0 ((first 1).val + (second 1).val) =
      X 2 * pderiv 1 ((first 0).val + (second 0).val)
    rw [map_add, map_add, mul_add, mul_add, first_closed, second_closed]
  smul_mem' := by
    intro scalar pair closed
    change X 2 * pderiv 0 (scalar • (pair 1).val) = X 2 * pderiv 1 (scalar • (pair 0).val)
    rw [Derivation.map_smul, Derivation.map_smul, mul_smul_comm, mul_smul_comm, closed]

def lowerRadicalCycles (degree : ℕ) : Submodule ℂ (Fin 2 → HomogeneousPoly degree) where
  carrier := {pair | X 0 * pderiv 2 (pair 1).val = X 1 * pderiv 2 (pair 0).val}
  zero_mem' := by simp
  add_mem' := by
    intro first second first_closed second_closed
    change X 0 * pderiv 2 ((first 1).val + (second 1).val) =
      X 1 * pderiv 2 ((first 0).val + (second 0).val)
    rw [map_add, map_add, mul_add, mul_add, first_closed, second_closed]
  smul_mem' := by
    intro scalar pair closed
    change X 0 * pderiv 2 (scalar • (pair 1).val) = X 1 * pderiv 2 (scalar • (pair 0).val)
    rw [Derivation.map_smul, Derivation.map_smul, mul_smul_comm, mul_smul_comm, closed]

def binaryGradientPair {degree : ℕ} (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    Fin 2 → HomogeneousPoly degree := fun coordinate =>
  ⟨pderiv coordinate.castSucc (binaryPolynomialLift polynomial.val), by
    change (pderiv coordinate.castSucc (binaryPolynomialLift polynomial.val)).IsHomogeneous degree
    have homogeneous := polynomial.property.rename_isHomogeneous (f := Fin.castSucc)
    simpa only [Nat.add_sub_cancel, binaryPolynomialLift] using homogeneous.pderiv (i := coordinate.castSucc)⟩

theorem binaryGradientPair_closed {degree : ℕ} (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    binaryGradientPair polynomial ∈ planeRadicalCycles degree := by
  change X 2 * pderiv 0 (pderiv 1 (binaryPolynomialLift polynomial.val)) =
    X 2 * pderiv 1 (pderiv 0 (binaryPolynomialLift polynomial.val))
  rw [pderiv_commute 0 1]

def planeRadicalCoordinate (degree : ℕ) :
    (Fin 2 → HomogeneousPoly degree) →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) where
  toFun pair := ⟨(degree + 1 : ℂ)⁻¹ •
    (X 0 * binaryPolynomialRestrict (pair 0).val + X 1 * binaryPolynomialRestrict (pair 1).val), by
      have first := (isHomogeneous_X ℂ (0 : Fin 2)).mul
        (binaryPolynomialRestrict_homogeneous (pair 0).val (pair 0).property)
      have second := (isHomogeneous_X ℂ (1 : Fin 2)).mul
        (binaryPolynomialRestrict_homogeneous (pair 1).val (pair 1).property)
      change ((degree + 1 : ℂ)⁻¹ •
        (X 0 * binaryPolynomialRestrict (pair 0).val + X 1 * binaryPolynomialRestrict (pair 1).val)).IsHomogeneous (degree + 1)
      rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
      simpa only [Nat.add_comm] using (first.add second).C_mul (degree + 1 : ℂ)⁻¹⟩
  map_add' first second := by
    apply Subtype.ext
    change (degree + 1 : ℂ)⁻¹ •
      (X 0 * binaryPolynomialRestrict ((first 0).val + (second 0).val) +
        X 1 * binaryPolynomialRestrict ((first 1).val + (second 1).val)) =
      (degree + 1 : ℂ)⁻¹ • (X 0 * binaryPolynomialRestrict (first 0).val + X 1 * binaryPolynomialRestrict (first 1).val) +
      (degree + 1 : ℂ)⁻¹ • (X 0 * binaryPolynomialRestrict (second 0).val + X 1 * binaryPolynomialRestrict (second 1).val)
    simp only [map_add, Algebra.smul_def]
    ring
  map_smul' scalar pair := by
    apply Subtype.ext
    change (degree + 1 : ℂ)⁻¹ •
      (X 0 * binaryPolynomialRestrict (scalar • (pair 0).val) +
        X 1 * binaryPolynomialRestrict (scalar • (pair 1).val)) =
      scalar • ((degree + 1 : ℂ)⁻¹ •
        (X 0 * binaryPolynomialRestrict (pair 0).val + X 1 * binaryPolynomialRestrict (pair 1).val))
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes]
    ring

theorem planeRadicalCoordinate_normal {degree : ℕ} (pair : Fin 2 → HomogeneousPoly degree)
    (polynomial : Binary.HomogeneousPoly (degree + 1)) (potential : HomogeneousPoly degree)
    (first_eq : (pair 0).val = pderiv 0 (binaryPolynomialLift polynomial.val) + X 2 * pderiv 0 potential.val)
    (second_eq : (pair 1).val = pderiv 1 (binaryPolynomialLift polynomial.val) + X 2 * pderiv 1 potential.val) :
    planeRadicalCoordinate degree pair = polynomial := by
  apply Subtype.ext
  change (degree + 1 : ℂ)⁻¹ •
    (X 0 * binaryPolynomialRestrict (pair 0).val + X 1 * binaryPolynomialRestrict (pair 1).val) = polynomial.val
  rw [first_eq, second_eq, binaryPolynomialRestrict_plane_first, binaryPolynomialRestrict_plane_second]
  have euler := polynomial.property.sum_X_mul_pderiv
  rw [Fin.sum_univ_two, ← Nat.cast_smul_eq_nsmul ℂ] at euler
  rw [euler, smul_smul]
  have nonzero : ((degree + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero degree)
  simp only [← Nat.cast_add_one, inv_mul_cancel₀ nonzero, one_smul]

theorem planeRadicalCoordinate_has_normal {degree : ℕ} (pair : planeRadicalCycles degree) :
    ∃ potential : HomogeneousPoly degree,
      (pair.val 0).val = pderiv 0 (binaryPolynomialLift (planeRadicalCoordinate degree pair.val).val) +
        X 2 * pderiv 0 potential.val ∧
      (pair.val 1).val = pderiv 1 (binaryPolynomialLift (planeRadicalCoordinate degree pair.val).val) +
        X 2 * pderiv 1 potential.val := by
  obtain ⟨polynomial, potential, first_eq, second_eq⟩ :=
    planeRadical_normal_form (pair.val 0) (pair.val 1) pair.property
  rw [planeRadicalCoordinate_normal pair.val polynomial potential first_eq second_eq]
  exact ⟨potential, first_eq, second_eq⟩

theorem planeRadicalCoordinate_gradient {degree : ℕ} (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    planeRadicalCoordinate degree (binaryGradientPair polynomial) = polynomial := by
  apply planeRadicalCoordinate_normal _ polynomial 0
  · simp [binaryGradientPair]
  · simp [binaryGradientPair]

def planeRadicalCycleCoordinate (degree : ℕ) :
    planeRadicalCycles degree →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (planeRadicalCoordinate degree).comp (planeRadicalCycles degree).subtype

theorem planeRadicalCycleCoordinate_surjective (degree : ℕ) :
    Function.Surjective (planeRadicalCycleCoordinate degree) := by
  intro polynomial
  exact ⟨⟨binaryGradientPair polynomial, binaryGradientPair_closed polynomial⟩,
    planeRadicalCoordinate_gradient polynomial⟩

theorem planeRadicalCycleCoordinate_kernel {degree : ℕ} (pair : planeRadicalCycles degree) :
    planeRadicalCycleCoordinate degree pair = 0 ↔
      ∃ potential : HomogeneousPoly degree,
        (pair.val 0).val = X 2 * pderiv 0 potential.val ∧
        (pair.val 1).val = X 2 * pderiv 1 potential.val := by
  obtain ⟨potential, first_eq, second_eq⟩ := planeRadicalCoordinate_has_normal pair
  exact planeRadical_normal_form_zero_iff (pair.val 0) (pair.val 1)
    (planeRadicalCoordinate degree pair.val) potential first_eq second_eq

end TernaryPeriodPolynomials.SphericalDetection.Helpers
