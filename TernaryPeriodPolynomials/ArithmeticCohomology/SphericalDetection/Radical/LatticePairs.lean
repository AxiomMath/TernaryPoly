module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.Lattice
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CoordinateEquivariance

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

def radicalLatticeGenerator (coordinate : Fin 2) : RadicalLattice :=
  if coordinate = 0 then radicalLatticeFirst else radicalLatticeSecond

def upperRadicalAverageEquiv (degree : ℕ) (coordinate : Fin 2) :
    HomogeneousPoly degree ≃ₗ[ℂ] HomogeneousPoly degree :=
  nilpotentAverageEquiv (upperRadicalGenerator degree coordinate)
    ⟨degree + 1, upperRadicalGenerator_power_zero degree coordinate⟩ degree

def lowerRadicalAverageEquiv (degree : ℕ) (coordinate : Fin 2) :
    HomogeneousPoly degree ≃ₗ[ℂ] HomogeneousPoly degree :=
  nilpotentAverageEquiv (lowerRadicalGenerator degree coordinate)
    ⟨degree + 1, lowerRadicalGenerator_power_zero degree coordinate⟩ degree

def upperRadicalCocyclePair (degree : ℕ) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) →ₗ[ℂ]
      (Fin 2 → HomogeneousPoly degree) where
  toFun cycle coordinate := (upperRadicalAverageEquiv degree coordinate).symm (cycle (radicalLatticeGenerator coordinate))
  map_add' first second := by
    funext coordinate
    exact map_add (upperRadicalAverageEquiv degree coordinate).symm
      (first (radicalLatticeGenerator coordinate)) (second (radicalLatticeGenerator coordinate))
  map_smul' scalar cycle := by
    funext coordinate
    exact map_smul (upperRadicalAverageEquiv degree coordinate).symm scalar
      (cycle (radicalLatticeGenerator coordinate))

def lowerRadicalCocyclePair (degree : ℕ) :
    groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) →ₗ[ℂ]
      (Fin 2 → HomogeneousPoly degree) where
  toFun cycle coordinate := (lowerRadicalAverageEquiv degree coordinate).symm (cycle (radicalLatticeGenerator coordinate))
  map_add' first second := by
    funext coordinate
    exact map_add (lowerRadicalAverageEquiv degree coordinate).symm
      (first (radicalLatticeGenerator coordinate)) (second (radicalLatticeGenerator coordinate))
  map_smul' scalar cycle := by
    funext coordinate
    exact map_smul (lowerRadicalAverageEquiv degree coordinate).symm scalar
      (cycle (radicalLatticeGenerator coordinate))

theorem upperRadicalCocyclePair_average {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) (coordinate : Fin 2) :
    nilpotentExponentialAverage (upperRadicalGenerator degree coordinate) (degree + 1)
      (upperRadicalCocyclePair degree cycle coordinate) = cycle (radicalLatticeGenerator coordinate) :=
  (upperRadicalAverageEquiv degree coordinate).apply_symm_apply _

theorem lowerRadicalCocyclePair_average {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) (coordinate : Fin 2) :
    nilpotentExponentialAverage (lowerRadicalGenerator degree coordinate) (degree + 1)
      (lowerRadicalCocyclePair degree cycle coordinate) = cycle (radicalLatticeGenerator coordinate) :=
  (lowerRadicalAverageEquiv degree coordinate).apply_symm_apply _

theorem exp_sub_one_closed_inst_irrel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (i₁ i₂ : Module ℚ (Module.End ℂ V)) (g h : Module.End ℂ V) (x y : V)
    (closed : (@IsNilpotent.exp _ _ i₁ g - 1) x = (@IsNilpotent.exp _ _ i₁ h - 1) y) :
    (@IsNilpotent.exp _ _ i₂ g - 1) x = (@IsNilpotent.exp _ _ i₂ h - 1) y := by
  cases Subsingleton.elim i₁ i₂
  exact closed

theorem upperRadicalCocyclePair_closed {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalCocyclePair degree cycle ∈ planeRadicalCycles degree := by
  have closed := oneCocycle_generator_closed (upperRadicalLatticeRep degree) cycle
    radicalLatticeFirst radicalLatticeSecond (Commute.all _ _)
  rw [upperRadicalLatticeRep_first, upperRadicalLatticeRep_second] at closed
  have first := upperRadicalCocyclePair_average cycle (0 : Fin 2)
  have second := upperRadicalCocyclePair_average cycle (1 : Fin 2)
  change _ = cycle radicalLatticeFirst at first
  change _ = cycle radicalLatticeSecond at second
  rw [← first, ← second] at closed
  have infinitesimal := (nilpotent_difference_pair_closed_iff
    (upperRadicalGenerator degree 0) (upperRadicalGenerator degree 1)
    (upperRadicalGenerators_commute degree) degree degree
    (upperRadicalGenerator_power_zero degree 0) (upperRadicalGenerator_power_zero degree 1)
    (upperRadicalCocyclePair degree cycle 0) (upperRadicalCocyclePair degree cycle 1)).mp
    (exp_sub_one_closed_inst_irrel _ _ _ _ _ _ closed)
  have values := congrArg (fun value : HomogeneousPoly degree => value.val) infinitesimal
  change (-1 : ℂ) • (X 2 * pderiv 0 (upperRadicalCocyclePair degree cycle 1).val) =
    (-1 : ℂ) • (X 2 * pderiv 1 (upperRadicalCocyclePair degree cycle 0).val) at values
  change X 2 * pderiv 0 (upperRadicalCocyclePair degree cycle 1).val =
    X 2 * pderiv 1 (upperRadicalCocyclePair degree cycle 0).val
  simpa only [neg_smul, one_smul, neg_inj] using values

theorem lowerRadicalCocyclePair_closed {degree : ℕ}
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalCocyclePair degree cycle ∈ lowerRadicalCycles degree := by
  have closed := oneCocycle_generator_closed (lowerRadicalLatticeRep degree) cycle
    radicalLatticeFirst radicalLatticeSecond (Commute.all _ _)
  rw [lowerRadicalLatticeRep_first, lowerRadicalLatticeRep_second] at closed
  have first := lowerRadicalCocyclePair_average cycle (0 : Fin 2)
  have second := lowerRadicalCocyclePair_average cycle (1 : Fin 2)
  change _ = cycle radicalLatticeFirst at first
  change _ = cycle radicalLatticeSecond at second
  rw [← first, ← second] at closed
  have infinitesimal := (nilpotent_difference_pair_closed_iff
    (lowerRadicalGenerator degree 0) (lowerRadicalGenerator degree 1)
    (lowerRadicalGenerators_commute degree) degree degree
    (lowerRadicalGenerator_power_zero degree 0) (lowerRadicalGenerator_power_zero degree 1)
    (lowerRadicalCocyclePair degree cycle 0) (lowerRadicalCocyclePair degree cycle 1)).mp
    (exp_sub_one_closed_inst_irrel _ _ _ _ _ _ closed)
  have values := congrArg (fun value : HomogeneousPoly degree => value.val) infinitesimal
  change (-3 : ℂ) • (X 0 * pderiv 2 (lowerRadicalCocyclePair degree cycle 1).val) =
    (-3 : ℂ) • (X 1 * pderiv 2 (lowerRadicalCocyclePair degree cycle 0).val) at values
  exact (smul_right_injective _ (by norm_num : (-3 : ℂ) ≠ 0)) values

def upperRadicalCocycleToInfinitesimal (degree : ℕ) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) →ₗ[ℂ] planeRadicalCycles degree :=
  (upperRadicalCocyclePair degree).codRestrict _ upperRadicalCocyclePair_closed

def lowerRadicalCocycleToInfinitesimal (degree : ℕ) :
    groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) →ₗ[ℂ] lowerRadicalCycles degree :=
  (lowerRadicalCocyclePair degree).codRestrict _ lowerRadicalCocyclePair_closed

end TernaryPeriodPolynomials.SphericalDetection.Helpers
