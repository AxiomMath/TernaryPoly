module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.GeneratorLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticeEquivalence

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

def upperRadicalCocycleLevi (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) →ₗ[ℂ]
      groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) :=
  oneCocyclePullback _ _ (upperLeviLatticeInput matrix) (arithmeticLeviCoefficient degree matrix)
    (upperLeviLatticeInput_intertwines degree matrix)

def lowerRadicalCocycleLevi (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) →ₗ[ℂ]
      groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) :=
  oneCocyclePullback _ _ (lowerLeviLatticeInput matrix) (arithmeticLeviCoefficient degree matrix)
    (lowerLeviLatticeInput_intertwines degree matrix)

theorem upperRadicalCocycleLevi_apply (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) (element : RadicalLattice) :
    upperRadicalCocycleLevi degree matrix cycle element =
      arithmeticLeviCoefficient degree matrix (cycle (upperLeviLatticeInput matrix element)) := rfl

theorem lowerRadicalCocycleLevi_apply (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) (element : RadicalLattice) :
    lowerRadicalCocycleLevi degree matrix cycle element =
      arithmeticLeviCoefficient degree matrix (cycle (lowerLeviLatticeInput matrix element)) := rfl

theorem upperRadicalCocyclePair_generator_closed {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalGenerator degree 0 (upperRadicalCocyclePair degree cycle 1) =
      upperRadicalGenerator degree 1 (upperRadicalCocyclePair degree cycle 0) := by
  have closed := upperRadicalCocyclePair_closed cycle
  change X 2 * pderiv 0 (upperRadicalCocyclePair degree cycle 1).val =
    X 2 * pderiv 1 (upperRadicalCocyclePair degree cycle 0).val at closed
  apply Subtype.ext
  exact congrArg (fun polynomial : Poly => (-1 : ℂ) • polynomial) closed

theorem lowerRadicalCocyclePair_generator_closed {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalGenerator degree 0 (lowerRadicalCocyclePair degree cycle 1) =
      lowerRadicalGenerator degree 1 (lowerRadicalCocyclePair degree cycle 0) := by
  have closed := lowerRadicalCocyclePair_closed cycle
  change X 0 * pderiv 2 (lowerRadicalCocyclePair degree cycle 1).val =
    X 1 * pderiv 2 (lowerRadicalCocyclePair degree cycle 0).val at closed
  apply Subtype.ext
  exact congrArg (fun polynomial : Poly => (-3 : ℂ) • polynomial) closed

theorem upperRadicalCocyclePair_levi {degree : ℕ} (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) (coordinate : Fin 2) :
    upperRadicalCocyclePair degree (upperRadicalCocycleLevi degree matrix cycle) coordinate =
      arithmeticLeviCoefficient degree matrix
        ((matrix⁻¹.val 0 coordinate : ℂ) • upperRadicalCocyclePair degree cycle 0 +
          (matrix⁻¹.val 1 coordinate : ℂ) • upperRadicalCocyclePair degree cycle 1) := by
  have equality := latticeCocycle_direction_natural (upperRadicalLatticeRep degree) cycle
    (upperRadicalGenerator degree 0) (upperRadicalGenerator degree 1)
    (upperRadicalCocyclePair degree cycle 0) (upperRadicalCocyclePair degree cycle 1)
    (upperRadicalGenerators_commute degree) (upperRadicalCocyclePair_generator_closed cycle)
    degree degree (upperRadicalGenerator_power_zero degree 0) (upperRadicalGenerator_power_zero degree 1)
    ((upperRadicalLatticeRep_first degree).trans (exp_inst_irrel _ _ _))
    ((upperRadicalLatticeRep_second degree).trans (exp_inst_irrel _ _ _))
    (upperRadicalCocyclePair_average cycle 0).symm (upperRadicalCocyclePair_average cycle 1).symm
    (upperRadicalGenerator degree coordinate) (arithmeticLeviCoefficient degree matrix)
    (arithmeticLeviCoefficient_injective degree matrix)
    (upperLeviLatticeInput matrix (radicalLatticeGenerator coordinate))
    (upperRadicalGenerator_arithmeticLevi degree matrix coordinate)
    degree (upperRadicalGenerator_power_zero degree coordinate)
  change upperRadicalCocyclePair degree (upperRadicalCocycleLevi degree matrix cycle) coordinate =
    arithmeticLeviCoefficient degree matrix
      (((upperLeviLatticeInput matrix (radicalLatticeGenerator coordinate)).toAdd.1 : ℂ) •
          upperRadicalCocyclePair degree cycle 0 +
        ((upperLeviLatticeInput matrix (radicalLatticeGenerator coordinate)).toAdd.2 : ℂ) •
          upperRadicalCocyclePair degree cycle 1) at equality
  rw [upperLeviLatticeInput_generator] at equality
  exact equality

theorem lowerRadicalCocyclePair_levi {degree : ℕ} (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) (coordinate : Fin 2) :
    lowerRadicalCocyclePair degree (lowerRadicalCocycleLevi degree matrix cycle) coordinate =
      arithmeticLeviCoefficient degree matrix
        ((matrix.val coordinate 0 : ℂ) • lowerRadicalCocyclePair degree cycle 0 +
          (matrix.val coordinate 1 : ℂ) • lowerRadicalCocyclePair degree cycle 1) := by
  have equality := latticeCocycle_direction_natural (lowerRadicalLatticeRep degree) cycle
    (lowerRadicalGenerator degree 0) (lowerRadicalGenerator degree 1)
    (lowerRadicalCocyclePair degree cycle 0) (lowerRadicalCocyclePair degree cycle 1)
    (lowerRadicalGenerators_commute degree) (lowerRadicalCocyclePair_generator_closed cycle)
    degree degree (lowerRadicalGenerator_power_zero degree 0) (lowerRadicalGenerator_power_zero degree 1)
    ((lowerRadicalLatticeRep_first degree).trans (exp_inst_irrel _ _ _))
    ((lowerRadicalLatticeRep_second degree).trans (exp_inst_irrel _ _ _))
    (lowerRadicalCocyclePair_average cycle 0).symm (lowerRadicalCocyclePair_average cycle 1).symm
    (lowerRadicalGenerator degree coordinate) (arithmeticLeviCoefficient degree matrix)
    (arithmeticLeviCoefficient_injective degree matrix)
    (lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate))
    (lowerRadicalGenerator_arithmeticLevi degree matrix coordinate)
    degree (lowerRadicalGenerator_power_zero degree coordinate)
  change lowerRadicalCocyclePair degree (lowerRadicalCocycleLevi degree matrix cycle) coordinate =
    arithmeticLeviCoefficient degree matrix
      (((lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate)).toAdd.1 : ℂ) •
          lowerRadicalCocyclePair degree cycle 0 +
        ((lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate)).toAdd.2 : ℂ) •
          lowerRadicalCocyclePair degree cycle 1) at equality
  rw [lowerLeviLatticeInput_generator] at equality
  exact equality

theorem upperRadicalCocycleToInfinitesimal_equivariant {degree : ℕ}
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalCocycleToInfinitesimal degree (upperRadicalCocycleLevi degree matrix cycle) =
      planeRadicalCycleLevi degree (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (upperRadicalCocycleToInfinitesimal degree cycle) := by
  apply Subtype.ext
  funext coordinate
  apply Subtype.ext
  change (upperRadicalCocyclePair degree (upperRadicalCocycleLevi degree matrix cycle) coordinate).val =
    planeRadicalLeviPair (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
      (fun index => (upperRadicalCocyclePair degree cycle index).val) coordinate
  rw [upperRadicalCocyclePair_levi, arithmeticLeviCoefficient_homogeneous]
  simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, homogeneousAction_coe,
    planeRadicalLeviPair, Fin.sum_univ_two, ← map_inv, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rfl

theorem lowerRadicalCocycleToInfinitesimal_equivariant {degree : ℕ}
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalCocycleToInfinitesimal degree (lowerRadicalCocycleLevi degree matrix cycle) =
      lowerRadicalCycleLevi degree (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (lowerRadicalCocycleToInfinitesimal degree cycle) := by
  apply Subtype.ext
  funext coordinate
  apply Subtype.ext
  change (lowerRadicalCocyclePair degree (lowerRadicalCocycleLevi degree matrix cycle) coordinate).val =
    lowerRadicalLeviPair (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
      (fun index => (lowerRadicalCocyclePair degree cycle index).val) coordinate
  rw [lowerRadicalCocyclePair_levi, arithmeticLeviCoefficient_homogeneous]
  simp only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, homogeneousAction_coe,
    lowerRadicalLeviPair, Fin.sum_univ_two, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rfl

theorem upperRadicalCocycleCoordinate_equivariant {degree : ℕ}
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalCocycleCoordinate degree (upperRadicalCocycleLevi degree matrix cycle) =
      Binary.homogeneousAction (degree + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (upperRadicalCocycleCoordinate degree cycle) := by
  change planeRadicalCycleCoordinate degree
      (upperRadicalCocycleToInfinitesimal degree (upperRadicalCocycleLevi degree matrix cycle)) = _
  rw [upperRadicalCocycleToInfinitesimal_equivariant, planeRadicalCycleCoordinate_equivariant]
  rfl

theorem lowerRadicalCocycleCoordinate_equivariant {degree : ℕ}
    (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalCocycleCoordinate degree (lowerRadicalCocycleLevi degree matrix cycle) =
      Binary.homogeneousAction (degree + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (lowerRadicalCocycleCoordinate degree cycle) := by
  change lowerRadicalCycleCoordinate degree
      (lowerRadicalCocycleToInfinitesimal degree (lowerRadicalCocycleLevi degree matrix cycle)) = _
  rw [lowerRadicalCocycleToInfinitesimal_equivariant, lowerRadicalCycleCoordinate_equivariant]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
