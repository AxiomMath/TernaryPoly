module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CohomologyCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem planeRadicalLeviPair_smul (matrix : Binary.GL2) (scalar : ℂ) (pair : Fin 2 → Poly)
    (coordinate : Fin 2) :
    planeRadicalLeviPair matrix (scalar • pair) coordinate =
      scalar • planeRadicalLeviPair matrix pair coordinate := by
  simp [planeRadicalLeviPair]

theorem lowerRadicalLeviPair_add (matrix : Binary.GL2) (first second : Fin 2 → Poly)
    (coordinate : Fin 2) :
    lowerRadicalLeviPair matrix (first + second) coordinate =
      lowerRadicalLeviPair matrix first coordinate + lowerRadicalLeviPair matrix second coordinate := by
  simp [lowerRadicalLeviPair, mul_add, Finset.sum_add_distrib]

theorem lowerRadicalLeviPair_smul (matrix : Binary.GL2) (scalar : ℂ) (pair : Fin 2 → Poly)
    (coordinate : Fin 2) :
    lowerRadicalLeviPair matrix (scalar • pair) coordinate =
      scalar • lowerRadicalLeviPair matrix pair coordinate := by
  simp [lowerRadicalLeviPair]

def planeRadicalCycleLevi (degree : ℕ) (matrix : Binary.GL2) :
    planeRadicalCycles degree →ₗ[ℂ] planeRadicalCycles degree where
  toFun pair := ⟨(fun coordinate =>
    ⟨planeRadicalLeviPair matrix (fun index => (pair.val index).val) coordinate,
      planeRadicalLeviPair_homogeneous matrix _ (fun index => (pair.val index).property) coordinate⟩),
    by
      change X 2 * pderiv 0 (planeRadicalLeviPair matrix (fun index => (pair.val index).val) 1) =
        X 2 * pderiv 1 (planeRadicalLeviPair matrix (fun index => (pair.val index).val) 0)
      exact planeRadicalLeviPair_closed matrix (fun index => (pair.val index).val) pair.property⟩
  map_add' first second := by
    apply Subtype.ext
    funext coordinate
    apply Subtype.ext
    exact planeRadicalLeviPair_add matrix (fun index => (first.val index).val)
      (fun index => (second.val index).val) coordinate
  map_smul' scalar pair := by
    apply Subtype.ext
    funext coordinate
    apply Subtype.ext
    exact planeRadicalLeviPair_smul matrix scalar (fun index => (pair.val index).val) coordinate

def lowerRadicalCycleLevi (degree : ℕ) (matrix : Binary.GL2) :
    lowerRadicalCycles degree →ₗ[ℂ] lowerRadicalCycles degree where
  toFun pair := ⟨(fun coordinate =>
    ⟨lowerRadicalLeviPair matrix (fun index => (pair.val index).val) coordinate,
      lowerRadicalLeviPair_homogeneous matrix _ (fun index => (pair.val index).property) coordinate⟩),
    by
      change X 0 * pderiv 2 (lowerRadicalLeviPair matrix (fun index => (pair.val index).val) 1) =
        X 1 * pderiv 2 (lowerRadicalLeviPair matrix (fun index => (pair.val index).val) 0)
      exact lowerRadicalLeviPair_closed matrix (fun index => (pair.val index).val) pair.property⟩
  map_add' first second := by
    apply Subtype.ext
    funext coordinate
    apply Subtype.ext
    exact lowerRadicalLeviPair_add matrix (fun index => (first.val index).val)
      (fun index => (second.val index).val) coordinate
  map_smul' scalar pair := by
    apply Subtype.ext
    funext coordinate
    apply Subtype.ext
    exact lowerRadicalLeviPair_smul matrix scalar (fun index => (pair.val index).val) coordinate

theorem planeRadicalCycleCoordinate_equivariant {degree : ℕ} (matrix : Binary.GL2)
    (pair : planeRadicalCycles degree) :
    planeRadicalCycleCoordinate degree (planeRadicalCycleLevi degree matrix pair) =
      Binary.homogeneousAction (degree + 1) (-1) matrix (planeRadicalCycleCoordinate degree pair) := by
  obtain ⟨potential, first_eq, second_eq⟩ := planeRadicalCoordinate_has_normal pair
  have pair_eq : (fun index => (pair.val index).val) = fun index : Fin 2 =>
      pderiv index.castSucc (binaryPolynomialLift (planeRadicalCycleCoordinate degree pair).val) +
        X 2 * pderiv index.castSucc potential.val := by
    funext index
    fin_cases index
    · exact first_eq
    · exact second_eq
  apply planeRadicalCoordinate_normal (planeRadicalCycleLevi degree matrix pair).val
    (Binary.homogeneousAction (degree + 1) (-1) matrix (planeRadicalCycleCoordinate degree pair))
    (homogeneousAction degree (-1) (planeLevi matrix 1) potential)
  · change planeRadicalLeviPair matrix (fun index => (pair.val index).val) 0 =
      pderiv 0 (binaryPolynomialLift (Binary.action (-1) matrix (planeRadicalCycleCoordinate degree pair).val)) +
        X 2 * pderiv 0 (action (-1) (planeLevi matrix 1) potential.val)
    rw [pair_eq]
    exact planeRadicalLeviPair_normal matrix _ potential.val 0
  · change planeRadicalLeviPair matrix (fun index => (pair.val index).val) 1 =
      pderiv 1 (binaryPolynomialLift (Binary.action (-1) matrix (planeRadicalCycleCoordinate degree pair).val)) +
        X 2 * pderiv 1 (action (-1) (planeLevi matrix 1) potential.val)
    rw [pair_eq]
    exact planeRadicalLeviPair_normal matrix _ potential.val 1

theorem lowerRadicalCycleCoordinate_equivariant {degree : ℕ} (matrix : Binary.GL2)
    (pair : lowerRadicalCycles degree) :
    lowerRadicalCycleCoordinate degree (lowerRadicalCycleLevi degree matrix pair) =
      Binary.homogeneousAction (degree + 1) 0 matrix (lowerRadicalCycleCoordinate degree pair) := by
  apply Subtype.ext
  apply binaryPolynomialLift_injective
  rw [lowerRadicalCycleCoordinate_lift]
  exact lowerRadicalLeviPair_binary matrix (fun index => (pair.val index).val)
    (lowerRadicalCycleCoordinate degree pair).val (lowerRadicalCycleCoordinate_lift pair).symm

theorem planeRadicalCycleLevi_preserves_boundaries {degree : ℕ} (matrix : Binary.GL2)
    (pair : planeRadicalCycles degree)
    (boundary : ∃ potential : HomogeneousPoly degree,
      (pair.val 0).val = X 2 * pderiv 0 potential.val ∧
      (pair.val 1).val = X 2 * pderiv 1 potential.val) :
    ∃ potential : HomogeneousPoly degree,
      ((planeRadicalCycleLevi degree matrix pair).val 0).val = X 2 * pderiv 0 potential.val ∧
      ((planeRadicalCycleLevi degree matrix pair).val 1).val = X 2 * pderiv 1 potential.val := by
  apply (planeRadicalCycleCoordinate_kernel _).mp
  rw [planeRadicalCycleCoordinate_equivariant, (planeRadicalCycleCoordinate_kernel pair).mpr boundary, map_zero]

theorem lowerRadicalCycleLevi_preserves_boundaries {degree : ℕ} (positive : 0 < degree)
    (matrix : Binary.GL2) (pair : lowerRadicalCycles degree)
    (boundary : ∃ potential : HomogeneousPoly degree,
      (pair.val 0).val = X 0 * pderiv 2 potential.val ∧
      (pair.val 1).val = X 1 * pderiv 2 potential.val) :
    ∃ potential : HomogeneousPoly degree,
      ((lowerRadicalCycleLevi degree matrix pair).val 0).val = X 0 * pderiv 2 potential.val ∧
      ((lowerRadicalCycleLevi degree matrix pair).val 1).val = X 1 * pderiv 2 potential.val := by
  apply (lowerRadicalCycleCoordinate_kernel positive _).mp
  rw [lowerRadicalCycleCoordinate_equivariant,
    (lowerRadicalCycleCoordinate_kernel positive pair).mpr boundary, map_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
