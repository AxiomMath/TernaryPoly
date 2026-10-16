module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticeLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OneCocyclePullback
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SurjectiveLinearDescent

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Binary coordinates on the actual upper arithmetic radical cohomology. -/
def upperRadicalH1Coordinate (degree : ℕ) :
    groupCohomology.H1 (upperRadicalLatticeRep degree) ≃ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  surjectiveLinearCoordinateEquiv (groupCohomology.H1π (upperRadicalLatticeRep degree)).hom
    (oneCocycle_H1_surjective _) (upperRadicalCocycleCoordinate degree)
    (upperRadicalCocycleCoordinate_surjective degree)
    (fun first second => (upperRadicalCocycleCoordinate_eq_iff first second).symm)

/-- Binary coordinates on the actual lower arithmetic radical cohomology. -/
def lowerRadicalH1Coordinate (degree : ℕ) (positive : 0 < degree) :
    groupCohomology.H1 (lowerRadicalLatticeRep degree) ≃ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  surjectiveLinearCoordinateEquiv (groupCohomology.H1π (lowerRadicalLatticeRep degree)).hom
    (oneCocycle_H1_surjective _) (lowerRadicalCocycleCoordinate degree)
    (lowerRadicalCocycleCoordinate_surjective degree)
    (fun first second => (lowerRadicalCocycleCoordinate_eq_iff positive first second).symm)

theorem upperRadicalH1Coordinate_apply {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalH1Coordinate degree (groupCohomology.H1π (upperRadicalLatticeRep degree) cycle) =
      upperRadicalCocycleCoordinate degree cycle :=
  surjectiveLinearCoordinateEquiv_apply (groupCohomology.H1π (upperRadicalLatticeRep degree)).hom
    (oneCocycle_H1_surjective _) (upperRadicalCocycleCoordinate degree)
    (upperRadicalCocycleCoordinate_surjective degree)
    (fun first second => (upperRadicalCocycleCoordinate_eq_iff first second).symm) cycle

theorem lowerRadicalH1Coordinate_apply {degree : ℕ} (positive : 0 < degree)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalH1Coordinate degree positive (groupCohomology.H1π (lowerRadicalLatticeRep degree) cycle) =
      lowerRadicalCocycleCoordinate degree cycle :=
  surjectiveLinearCoordinateEquiv_apply (groupCohomology.H1π (lowerRadicalLatticeRep degree)).hom
    (oneCocycle_H1_surjective _) (lowerRadicalCocycleCoordinate degree)
    (lowerRadicalCocycleCoordinate_surjective degree)
    (fun first second => (lowerRadicalCocycleCoordinate_eq_iff positive first second).symm) cycle

def upperRadicalH1Levi (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    Module.End ℂ (groupCohomology.H1 (upperRadicalLatticeRep degree)) :=
  oneCocyclePullbackH1 _ _ (upperLeviLatticeInput matrix) (arithmeticLeviCoefficient degree matrix)
    (upperLeviLatticeInput_intertwines degree matrix)

def lowerRadicalH1Levi (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    Module.End ℂ (groupCohomology.H1 (lowerRadicalLatticeRep degree)) :=
  oneCocyclePullbackH1 _ _ (lowerLeviLatticeInput matrix) (arithmeticLeviCoefficient degree matrix)
    (lowerLeviLatticeInput_intertwines degree matrix)

theorem upperRadicalH1Levi_apply {degree : ℕ} (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalH1Levi degree matrix (groupCohomology.H1π (upperRadicalLatticeRep degree) cycle) =
      groupCohomology.H1π (upperRadicalLatticeRep degree) (upperRadicalCocycleLevi degree matrix cycle) :=
  oneCocyclePullbackH1_apply (upperRadicalLatticeRep degree) (upperRadicalLatticeRep degree)
    (upperLeviLatticeInput matrix) (arithmeticLeviCoefficient degree matrix)
    (upperLeviLatticeInput_intertwines degree matrix) cycle

theorem lowerRadicalH1Levi_apply {degree : ℕ} (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalH1Levi degree matrix (groupCohomology.H1π (lowerRadicalLatticeRep degree) cycle) =
      groupCohomology.H1π (lowerRadicalLatticeRep degree) (lowerRadicalCocycleLevi degree matrix cycle) :=
  oneCocyclePullbackH1_apply (lowerRadicalLatticeRep degree) (lowerRadicalLatticeRep degree)
    (lowerLeviLatticeInput matrix) (arithmeticLeviCoefficient degree matrix)
    (lowerLeviLatticeInput_intertwines degree matrix) cycle

theorem upperRadicalH1Coordinate_equivariant {degree : ℕ}
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (cohomology : groupCohomology.H1 (upperRadicalLatticeRep degree)) :
    upperRadicalH1Coordinate degree (upperRadicalH1Levi degree matrix cohomology) =
      Binary.homogeneousAction (degree + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (upperRadicalH1Coordinate degree cohomology) := by
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (upperRadicalLatticeRep degree) cohomology
  rw [upperRadicalH1Levi_apply, upperRadicalH1Coordinate_apply, upperRadicalH1Coordinate_apply,
    upperRadicalCocycleCoordinate_equivariant]

theorem lowerRadicalH1Coordinate_equivariant {degree : ℕ} (positive : 0 < degree)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (cohomology : groupCohomology.H1 (lowerRadicalLatticeRep degree)) :
    lowerRadicalH1Coordinate degree positive (lowerRadicalH1Levi degree matrix cohomology) =
      Binary.homogeneousAction (degree + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (lowerRadicalH1Coordinate degree positive cohomology) := by
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (lowerRadicalLatticeRep degree) cohomology
  rw [lowerRadicalH1Levi_apply, lowerRadicalH1Coordinate_apply, lowerRadicalH1Coordinate_apply,
    lowerRadicalCocycleCoordinate_equivariant]

/-- The induced cohomology maps form the arithmetic Levi representation. -/
def upperRadicalH1LeviRepresentation (degree : ℕ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) ℤ)
      (groupCohomology.H1 (upperRadicalLatticeRep degree)) where
  toFun := upperRadicalH1Levi degree
  map_one' := by
    apply LinearMap.ext
    intro cohomology
    apply (upperRadicalH1Coordinate degree).injective
    rw [upperRadicalH1Coordinate_equivariant, map_one, map_one]
    rfl
  map_mul' first second := by
    apply LinearMap.ext
    intro cohomology
    apply (upperRadicalH1Coordinate degree).injective
    change upperRadicalH1Coordinate degree (upperRadicalH1Levi degree (first * second) cohomology) =
      upperRadicalH1Coordinate degree (upperRadicalH1Levi degree first (upperRadicalH1Levi degree second cohomology))
    rw [upperRadicalH1Coordinate_equivariant, upperRadicalH1Coordinate_equivariant,
      upperRadicalH1Coordinate_equivariant, map_mul, map_mul]
    rfl

def lowerRadicalH1LeviRepresentation (degree : ℕ) (positive : 0 < degree) :
    Representation ℂ (GeneralLinearGroup (Fin 2) ℤ)
      (groupCohomology.H1 (lowerRadicalLatticeRep degree)) where
  toFun := lowerRadicalH1Levi degree
  map_one' := by
    apply LinearMap.ext
    intro cohomology
    apply (lowerRadicalH1Coordinate degree positive).injective
    rw [lowerRadicalH1Coordinate_equivariant positive, map_one, map_one]
    rfl
  map_mul' first second := by
    apply LinearMap.ext
    intro cohomology
    apply (lowerRadicalH1Coordinate degree positive).injective
    change lowerRadicalH1Coordinate degree positive (lowerRadicalH1Levi degree (first * second) cohomology) =
      lowerRadicalH1Coordinate degree positive (lowerRadicalH1Levi degree first (lowerRadicalH1Levi degree second cohomology))
    rw [lowerRadicalH1Coordinate_equivariant positive, lowerRadicalH1Coordinate_equivariant positive,
      lowerRadicalH1Coordinate_equivariant positive, map_mul, map_mul]
    rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
