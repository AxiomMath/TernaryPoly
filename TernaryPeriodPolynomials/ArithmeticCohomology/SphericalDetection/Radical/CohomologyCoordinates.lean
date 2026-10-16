module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.HomogeneousCycles
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def lowerRadicalCoordinate (degree : ℕ) :
    (Fin 2 → HomogeneousPoly degree) →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) where
  toFun pair := ⟨binaryPolynomialRestrict (lowerRadicalContraction (pair 0).val (pair 1).val),
    binaryPolynomialRestrict_homogeneous _
      (lowerRadicalContraction_homogeneous _ _ (pair 0).property (pair 1).property)⟩
  map_add' first second := by
    apply Subtype.ext
    change binaryPolynomialRestrict
      (lowerRadicalContraction ((first 0).val + (second 0).val) ((first 1).val + (second 1).val)) =
      binaryPolynomialRestrict (lowerRadicalContraction (first 0).val (first 1).val) +
        binaryPolynomialRestrict (lowerRadicalContraction (second 0).val (second 1).val)
    simp only [lowerRadicalContraction, map_sub, map_add, map_mul]
    ring
  map_smul' scalar pair := by
    apply Subtype.ext
    change binaryPolynomialRestrict
      (lowerRadicalContraction (scalar • (pair 0).val) (scalar • (pair 1).val)) =
      scalar • binaryPolynomialRestrict (lowerRadicalContraction (pair 0).val (pair 1).val)
    simp only [lowerRadicalContraction, Algebra.smul_def, map_sub, map_mul, AlgHom.commutes]
    ring

def lowerRadicalCycleCoordinate (degree : ℕ) :
    lowerRadicalCycles degree →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (lowerRadicalCoordinate degree).comp (lowerRadicalCycles degree).subtype

theorem lowerRadicalCycleCoordinate_lift {degree : ℕ} (pair : lowerRadicalCycles degree) :
    binaryPolynomialLift (lowerRadicalCycleCoordinate degree pair).val =
      lowerRadicalContraction (pair.val 0).val (pair.val 1).val := by
  obtain ⟨polynomial, equality⟩ := lowerRadicalContraction_exists_binary
    (pair.val 0) (pair.val 1) pair.property
  change binaryPolynomialLift polynomial.val =
    lowerRadicalContraction (pair.val 0).val (pair.val 1).val at equality
  change binaryPolynomialLift
    (binaryPolynomialRestrict (lowerRadicalContraction (pair.val 0).val (pair.val 1).val)) = _
  rw [← equality, binaryPolynomialRestrict_lift]

theorem lowerRadicalCycleCoordinate_surjective (degree : ℕ) :
    Function.Surjective (lowerRadicalCycleCoordinate degree) := by
  intro polynomial
  obtain ⟨alpha, beta, closed, equality⟩ := lowerRadicalContraction_surjective polynomial
  let pair : lowerRadicalCycles degree := ⟨![alpha, beta], closed⟩
  refine ⟨pair, ?_⟩
  apply Subtype.ext
  apply binaryPolynomialLift_injective
  rw [lowerRadicalCycleCoordinate_lift]
  exact equality

theorem lowerRadicalCycleCoordinate_kernel {degree : ℕ} (positive : 0 < degree)
    (pair : lowerRadicalCycles degree) :
    lowerRadicalCycleCoordinate degree pair = 0 ↔
      ∃ potential : HomogeneousPoly degree,
        (pair.val 0).val = X 0 * pderiv 2 potential.val ∧
        (pair.val 1).val = X 1 * pderiv 2 potential.val := by
  rw [← lowerRadicalContraction_eq_zero_iff positive (pair.val 0) (pair.val 1)]
  constructor
  · intro zero
    rw [← lowerRadicalCycleCoordinate_lift, zero, Submodule.coe_zero, map_zero]
  · intro zero
    apply Subtype.ext
    change binaryPolynomialRestrict (lowerRadicalContraction (pair.val 0).val (pair.val 1).val) = 0
    rw [zero, map_zero]

/-- The infinitesimal plane quotient; the preceding kernel theorem identifies its exact boundaries. -/
abbrev PlaneRadicalQuotient (degree : ℕ) :=
  @HasQuotient.Quotient (planeRadicalCycles degree) (Submodule ℂ (planeRadicalCycles degree))
    (@Submodule.hasQuotient ℂ (planeRadicalCycles degree) inferInstance inferInstance inferInstance)
    (planeRadicalCycleCoordinate degree).ker

abbrev LowerRadicalQuotient (degree : ℕ) :=
  @HasQuotient.Quotient (lowerRadicalCycles degree) (Submodule ℂ (lowerRadicalCycles degree))
    (@Submodule.hasQuotient ℂ (lowerRadicalCycles degree) inferInstance inferInstance inferInstance)
    (lowerRadicalCycleCoordinate degree).ker

def planeRadicalQuotientEquiv (degree : ℕ) :
    PlaneRadicalQuotient degree ≃ₗ[ℂ]
      Binary.HomogeneousPoly (degree + 1) :=
  @LinearMap.quotKerEquivOfSurjective ℂ (planeRadicalCycles degree)
    (Binary.HomogeneousPoly (degree + 1)) inferInstance inferInstance inferInstance inferInstance inferInstance
    (planeRadicalCycleCoordinate degree) (planeRadicalCycleCoordinate_surjective degree)

/-- In positive degree its kernel is precisely the lower-radical boundary space. -/
def lowerRadicalQuotientEquiv (degree : ℕ) :
    LowerRadicalQuotient degree ≃ₗ[ℂ]
      Binary.HomogeneousPoly (degree + 1) :=
  @LinearMap.quotKerEquivOfSurjective ℂ (lowerRadicalCycles degree)
    (Binary.HomogeneousPoly (degree + 1)) inferInstance inferInstance inferInstance inferInstance inferInstance
    (lowerRadicalCycleCoordinate degree) (lowerRadicalCycleCoordinate_surjective degree)

theorem planeRadicalQuotientEquiv_mk {degree : ℕ} (pair : planeRadicalCycles degree) :
    planeRadicalQuotientEquiv degree (Submodule.Quotient.mk pair) =
      planeRadicalCycleCoordinate degree pair :=
  rfl

theorem lowerRadicalQuotientEquiv_mk {degree : ℕ} (pair : lowerRadicalCycles degree) :
    lowerRadicalQuotientEquiv degree (Submodule.Quotient.mk pair) =
      lowerRadicalCycleCoordinate degree pair :=
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
