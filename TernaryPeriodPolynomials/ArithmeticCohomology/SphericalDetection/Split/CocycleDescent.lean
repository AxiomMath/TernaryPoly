module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.InvariantInflation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.MixedNormalization

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

theorem twoCocycle_radical_second_right (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : groupCohomology.cocycles₂ representation)
    (right_zero : ∀ element radical, cycle (element, inclusion radical) = 0)
    (first second : E) (radical : N) : cycle (first, second * inclusion radical) = cycle (first, second) := by
  have equation := twoCocycle_relation representation cycle first second (inclusion radical)
  rw [right_zero, right_zero, map_zero, zero_add, zero_add] at equation
  exact equation.symm

theorem splitReducedCocycle_pair_left {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (left_zero : ∀ radical element, cycle (extension.inl radical, element) = 0)
    (right_zero : ∀ element radical, cycle (element, extension.inl radical) = 0)
    (radical : N) (first second : L) :
    cycle (extension.inl radical * splitting first, splitting second) = cycle (splitting first, splitting second) := by
  have equation := twoCocycle_relation representation cycle (splitting first)
    (extension.inl (splitRadicalInput splitting first radical)) (splitting second)
  rw [← splitRadicalInput_commute, left_zero, right_zero, map_zero, add_zero, zero_add] at equation
  rw [splitRadicalInput_commute splitting second,
    twoCocycle_radical_second_right extension.inl representation cycle right_zero] at equation
  exact equation

theorem splitReducedCocycle_invariant {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (left_zero : ∀ radical element, cycle (extension.inl radical, element) = 0)
    (right_zero : ∀ element radical, cycle (element, extension.inl radical) = 0)
    (first second : L) : cycle (splitting first, splitting second) ∈ (Rep.res extension.inl representation).ρ.invariants := by
  apply (Representation.mem_invariants _ _).mpr
  intro radical
  have equation := twoCocycle_relation representation cycle (extension.inl radical) (splitting first) (splitting second)
  rw [left_zero, left_zero, add_zero, add_zero,
    splitReducedCocycle_pair_left splitting representation cycle left_zero right_zero] at equation
  exact equation.symm

theorem splitReducedCocycle_pair {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (left_zero : ∀ radical element, cycle (extension.inl radical, element) = 0)
    (right_zero : ∀ element radical, cycle (element, extension.inl radical) = 0)
    (first_radical second_radical : N) (first_levi second_levi : L) :
    cycle (extension.inl first_radical * splitting first_levi, extension.inl second_radical * splitting second_levi) =
      cycle (splitting first_levi, splitting second_levi) := by
  rw [splitRadicalInput_commute splitting second_levi,
    twoCocycle_radical_second_right extension.inl representation cycle right_zero,
    splitReducedCocycle_pair_left splitting representation cycle left_zero right_zero]

theorem splitReducedCocycle_reconstruct {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (left_zero : ∀ radical element, cycle (extension.inl radical, element) = 0)
    (right_zero : ∀ element radical, cycle (element, extension.inl radical) = 0)
    (first second : E) :
    cycle (first, second) = cycle (splitting (extension.rightHom first), splitting (extension.rightHom second)) := by
  obtain ⟨first_radical, first_levi, rfl⟩ := split_exists_pair splitting first
  obtain ⟨second_radical, second_levi, rfl⟩ := split_exists_pair splitting second
  rw [splitReducedCocycle_pair splitting representation cycle left_zero right_zero]
  simp only [map_mul, extension.rightHom_inl, splitting.rightHom_splitting, one_mul]

/-- Descent of a cocycle vanishing in both radical slots to the invariant coefficient module. -/
def splitDescendedCocycle {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (left_zero : ∀ radical element, cycle (extension.inl radical, element) = 0)
    (right_zero : ∀ element radical, cycle (element, extension.inl radical) = 0) :
    groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation) :=
  ⟨fun pair => ⟨cycle (splitting pair.1, splitting pair.2),
      splitReducedCocycle_invariant splitting representation cycle left_zero right_zero pair.1 pair.2⟩, by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro first second third
    apply Subtype.ext
    change cycle (splitting (first * second), splitting third) + cycle (splitting first, splitting second) =
      representation.ρ (splitting first) (cycle (splitting second, splitting third)) +
        cycle (splitting first, splitting (second * third))
    rw [map_mul, map_mul]
    exact twoCocycle_relation representation cycle _ _ _⟩

theorem splitDescendedCocycle_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (left_zero : ∀ radical element, cycle (extension.inl radical, element) = 0)
    (right_zero : ∀ element radical, cycle (element, extension.inl radical) = 0) (first second : L) :
    (splitDescendedCocycle splitting representation cycle left_zero right_zero (first, second)).val =
      cycle (splitting first, splitting second) := rfl

theorem splitInflated_descended {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ representation)
    (left_zero : ∀ radical element, cycle (extension.inl radical, element) = 0)
    (right_zero : ∀ element radical, cycle (element, extension.inl radical) = 0) :
    splitInflatedCocycle splitting representation (splitDescendedCocycle splitting representation cycle left_zero right_zero) =
      cycle := by
  apply Subtype.ext
  funext pair
  change splitInflatedCocycle splitting representation
    (splitDescendedCocycle splitting representation cycle left_zero right_zero) (pair.1, pair.2) =
      cycle (pair.1, pair.2)
  rw [splitInflatedCocycle_apply, splitDescendedCocycle_apply]
  exact (splitReducedCocycle_reconstruct splitting representation cycle left_zero right_zero pair.1 pair.2).symm

theorem relativeTwoCocycle_inflation_of_edge_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (zero : groupCohomology.H1π (splitRadicalH1Representation splitting representation)
      (splitCocycleEdge splitting representation cycle) = 0) :
    ∃ levi_class : groupCohomology.H2 (splitInvariantRepresentation splitting representation),
      splitInvariantInflation splitting representation levi_class = groupCohomology.H2π representation cycle.val := by
  obtain ⟨normalized, same_class, left_zero, right_zero⟩ := splitEdge_radical_normalization splitting representation cycle zero
  refine ⟨groupCohomology.H2π _ (splitDescendedCocycle splitting representation normalized left_zero right_zero), ?_⟩
  rw [splitInvariantInflation_apply, splitInflated_descended]
  exact same_class

theorem splitCohomologyEdge_kernel_inflation {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cohomology : (twoCohomologyRestriction extension.inl representation).ker)
    (zero : splitCohomologyEdge splitting representation cohomology = 0) :
    ∃ levi_class : groupCohomology.H2 (splitInvariantRepresentation splitting representation),
      splitInvariantInflation splitting representation levi_class = cohomology.val := by
  obtain ⟨cycle, rfl⟩ := relativeTwoCocycleClass_surjective extension.inl extension.inl_injective representation cohomology
  rw [splitCohomologyEdge_apply] at zero
  exact relativeTwoCocycle_inflation_of_edge_zero splitting representation cycle zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
