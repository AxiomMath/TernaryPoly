module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticeCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleExtension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem upperRadicalCocycleToInfinitesimal_injective (degree : ℕ) :
    Function.Injective (upperRadicalCocycleToInfinitesimal degree) := by
  intro first second equality
  have pairs := congrArg Subtype.val equality
  apply oneCocycle_eq_of_two_generators (upperRadicalLatticeRep degree) first second
    radicalLatticeFirst radicalLatticeSecond radicalLattice_generated
  · have values := congrArg (fun pair : Fin 2 → HomogeneousPoly degree =>
      nilpotentExponentialAverage (upperRadicalGenerator degree 0) (degree + 1) (pair 0)) pairs
    simp only [upperRadicalCocycleToInfinitesimal, LinearMap.codRestrict_apply,
      upperRadicalCocyclePair_average, radicalLatticeGenerator, ite_true] at values
    exact values
  · have values := congrArg (fun pair : Fin 2 → HomogeneousPoly degree =>
      nilpotentExponentialAverage (upperRadicalGenerator degree 1) (degree + 1) (pair 1)) pairs
    simp only [upperRadicalCocycleToInfinitesimal, LinearMap.codRestrict_apply,
      upperRadicalCocyclePair_average, radicalLatticeGenerator, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at values
    exact values

theorem lowerRadicalCocycleToInfinitesimal_injective (degree : ℕ) :
    Function.Injective (lowerRadicalCocycleToInfinitesimal degree) := by
  intro first second equality
  have pairs := congrArg Subtype.val equality
  apply oneCocycle_eq_of_two_generators (lowerRadicalLatticeRep degree) first second
    radicalLatticeFirst radicalLatticeSecond radicalLattice_generated
  · have values := congrArg (fun pair : Fin 2 → HomogeneousPoly degree =>
      nilpotentExponentialAverage (lowerRadicalGenerator degree 0) (degree + 1) (pair 0)) pairs
    simp only [lowerRadicalCocycleToInfinitesimal, LinearMap.codRestrict_apply,
      lowerRadicalCocyclePair_average, radicalLatticeGenerator, ite_true] at values
    exact values
  · have values := congrArg (fun pair : Fin 2 → HomogeneousPoly degree =>
      nilpotentExponentialAverage (lowerRadicalGenerator degree 1) (degree + 1) (pair 1)) pairs
    simp only [lowerRadicalCocycleToInfinitesimal, LinearMap.codRestrict_apply,
      lowerRadicalCocyclePair_average, radicalLatticeGenerator, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at values
    exact values

theorem upperRadicalCocycleToInfinitesimal_surjective (degree : ℕ) :
    Function.Surjective (upperRadicalCocycleToInfinitesimal degree) := by
  intro pair
  let alpha := nilpotentExponentialAverage (upperRadicalGenerator degree 0) (degree + 1) (pair.val 0)
  let beta := nilpotentExponentialAverage (upperRadicalGenerator degree 1) (degree + 1) (pair.val 1)
  have infinitesimal : upperRadicalGenerator degree 0 (pair.val 1) =
      upperRadicalGenerator degree 1 (pair.val 0) := by
    apply Subtype.ext
    change (-1 : ℂ) • (X 2 * pderiv 0 (pair.val 1).val) =
      (-1 : ℂ) • (X 2 * pderiv 1 (pair.val 0).val)
    rw [pair.property]
  have closed : ((upperRadicalLatticeRep degree).ρ radicalLatticeFirst - 1) beta =
      ((upperRadicalLatticeRep degree).ρ radicalLatticeSecond - 1) alpha := by
    rw [upperRadicalLatticeRep_first, upperRadicalLatticeRep_second]
    exact exp_sub_one_closed_inst_irrel _ _ _ _ _ _
      ((nilpotent_difference_pair_closed_iff _ _ (upperRadicalGenerators_commute degree)
        degree degree (upperRadicalGenerator_power_zero degree 0) (upperRadicalGenerator_power_zero degree 1) _ _).mpr
        infinitesimal)
  let cycle := latticeCocycleOfClosedPair (upperRadicalLatticeRep degree) alpha beta closed
  refine ⟨cycle, ?_⟩
  apply Subtype.ext
  funext coordinate
  apply (upperRadicalAverageEquiv degree coordinate).injective
  change nilpotentExponentialAverage (upperRadicalGenerator degree coordinate) (degree + 1)
      (upperRadicalCocyclePair degree cycle coordinate) =
    nilpotentExponentialAverage (upperRadicalGenerator degree coordinate) (degree + 1) (pair.val coordinate)
  rw [upperRadicalCocyclePair_average]
  fin_cases coordinate
  · exact latticeCocycleOfClosedPair_first _ _ _ closed
  · exact latticeCocycleOfClosedPair_second _ _ _ closed

theorem lowerRadicalCocycleToInfinitesimal_surjective (degree : ℕ) :
    Function.Surjective (lowerRadicalCocycleToInfinitesimal degree) := by
  intro pair
  let alpha := nilpotentExponentialAverage (lowerRadicalGenerator degree 0) (degree + 1) (pair.val 0)
  let beta := nilpotentExponentialAverage (lowerRadicalGenerator degree 1) (degree + 1) (pair.val 1)
  have infinitesimal : lowerRadicalGenerator degree 0 (pair.val 1) =
      lowerRadicalGenerator degree 1 (pair.val 0) := by
    apply Subtype.ext
    change (-3 : ℂ) • (X 0 * pderiv 2 (pair.val 1).val) =
      (-3 : ℂ) • (X 1 * pderiv 2 (pair.val 0).val)
    rw [pair.property]
  have closed : ((lowerRadicalLatticeRep degree).ρ radicalLatticeFirst - 1) beta =
      ((lowerRadicalLatticeRep degree).ρ radicalLatticeSecond - 1) alpha := by
    rw [lowerRadicalLatticeRep_first, lowerRadicalLatticeRep_second]
    exact exp_sub_one_closed_inst_irrel _ _ _ _ _ _
      ((nilpotent_difference_pair_closed_iff _ _ (lowerRadicalGenerators_commute degree)
        degree degree (lowerRadicalGenerator_power_zero degree 0) (lowerRadicalGenerator_power_zero degree 1) _ _).mpr
        infinitesimal)
  let cycle := latticeCocycleOfClosedPair (lowerRadicalLatticeRep degree) alpha beta closed
  refine ⟨cycle, ?_⟩
  apply Subtype.ext
  funext coordinate
  apply (lowerRadicalAverageEquiv degree coordinate).injective
  change nilpotentExponentialAverage (lowerRadicalGenerator degree coordinate) (degree + 1)
      (lowerRadicalCocyclePair degree cycle coordinate) =
    nilpotentExponentialAverage (lowerRadicalGenerator degree coordinate) (degree + 1) (pair.val coordinate)
  rw [lowerRadicalCocyclePair_average]
  fin_cases coordinate
  · exact latticeCocycleOfClosedPair_first _ _ _ closed
  · exact latticeCocycleOfClosedPair_second _ _ _ closed

def upperRadicalCocycleEquiv (degree : ℕ) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep degree) ≃ₗ[ℂ] planeRadicalCycles degree :=
  LinearEquiv.ofBijective (upperRadicalCocycleToInfinitesimal degree)
    ⟨upperRadicalCocycleToInfinitesimal_injective degree, upperRadicalCocycleToInfinitesimal_surjective degree⟩

def lowerRadicalCocycleEquiv (degree : ℕ) :
    groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree) ≃ₗ[ℂ] lowerRadicalCycles degree :=
  LinearEquiv.ofBijective (lowerRadicalCocycleToInfinitesimal degree)
    ⟨lowerRadicalCocycleToInfinitesimal_injective degree, lowerRadicalCocycleToInfinitesimal_surjective degree⟩

theorem upperRadicalCocycleCoordinate_surjective (degree : ℕ) :
    Function.Surjective (upperRadicalCocycleCoordinate degree) :=
  (planeRadicalCycleCoordinate_surjective degree).comp (upperRadicalCocycleToInfinitesimal_surjective degree)

theorem lowerRadicalCocycleCoordinate_surjective (degree : ℕ) :
    Function.Surjective (lowerRadicalCocycleCoordinate degree) :=
  (lowerRadicalCycleCoordinate_surjective degree).comp (lowerRadicalCocycleToInfinitesimal_surjective degree)

theorem upperRadicalCocycleCoordinate_eq_iff {degree : ℕ}
    (first second : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) :
    upperRadicalCocycleCoordinate degree first = upperRadicalCocycleCoordinate degree second ↔
      groupCohomology.H1π (upperRadicalLatticeRep degree) first =
        groupCohomology.H1π (upperRadicalLatticeRep degree) second := by
  rw [← sub_eq_zero, ← map_sub, upperRadicalCocycleCoordinate_zero_iff, map_sub, sub_eq_zero]

theorem lowerRadicalCocycleCoordinate_eq_iff {degree : ℕ} (positive : 0 < degree)
    (first second : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) :
    lowerRadicalCocycleCoordinate degree first = lowerRadicalCocycleCoordinate degree second ↔
      groupCohomology.H1π (lowerRadicalLatticeRep degree) first =
        groupCohomology.H1π (lowerRadicalLatticeRep degree) second := by
  rw [← sub_eq_zero, ← map_sub, lowerRadicalCocycleCoordinate_zero_iff positive, map_sub, sub_eq_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
