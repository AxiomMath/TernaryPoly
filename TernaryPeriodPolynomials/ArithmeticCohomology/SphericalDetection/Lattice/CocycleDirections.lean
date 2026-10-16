module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.NilpotentLattice

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

def oneCocycleAugmentedOperator {G : Type} [Group G] (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (element : G) :
    Module.End ℂ (representation × ℂ) where
  toFun vector := (representation.ρ element vector.1 + vector.2 • cycle element, vector.2)
  map_add' first second := by simp [map_add, add_smul]; abel
  map_smul' scalar vector := by simp [map_smul, smul_add, mul_smul]

def oneCocycleAugmentedRepresentation {G : Type} [Group G] (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) :
    Representation ℂ G (representation × ℂ) where
  toFun := oneCocycleAugmentedOperator representation cycle
  map_one' := by
    apply LinearMap.ext
    intro vector
    change (representation.ρ 1 vector.1 + vector.2 • cycle 1, vector.2) = vector
    rw [map_one, Module.End.one_apply, groupCohomology.cocycles₁_map_one, smul_zero, add_zero]
  map_mul' first second := by
    apply LinearMap.ext
    intro vector
    change (representation.ρ (first * second) vector.1 + vector.2 • cycle (first * second), vector.2) =
      (representation.ρ first (representation.ρ second vector.1 + vector.2 • cycle second) +
        vector.2 • cycle first, vector.2)
    rw [map_mul, oneCocycle_mul, map_add, map_smul, smul_add, add_assoc]
    rfl

theorem oneCocycleAugmentedRepresentation_apply {G : Type} [Group G] (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₁ representation) (element : G) (vector : representation × ℂ) :
    oneCocycleAugmentedRepresentation representation cycle element vector =
      (representation.ρ element vector.1 + vector.2 • cycle element, vector.2) := rfl

/-- Generator averages determine the augmented representation in every lattice direction. -/
theorem latticeCocycle_augmented_exponential (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₁ representation)
    (first second : Module.End ℂ representation) (alpha beta : representation)
    (commute : Commute first second) (closed : first beta = second alpha)
    (first_cutoff second_cutoff : ℕ)
    (first_nilpotent : first ^ (first_cutoff + 1) = 0)
    (second_nilpotent : second ^ (second_cutoff + 1) = 0)
    (first_action : representation.ρ radicalLatticeFirst = IsNilpotent.exp first)
    (second_action : representation.ρ radicalLatticeSecond = IsNilpotent.exp second)
    (first_value : cycle radicalLatticeFirst = nilpotentExponentialAverage first (first_cutoff + 1) alpha)
    (second_value : cycle radicalLatticeSecond = nilpotentExponentialAverage second (second_cutoff + 1) beta)
    (element : RadicalLattice) :
    oneCocycleAugmentedRepresentation representation cycle element =
      IsNilpotent.exp (affineInfinitesimal (latticeInfinitesimal first second element)
        ((element.toAdd.1 : ℂ) • alpha + (element.toAdd.2 : ℂ) • beta)) := by
  let augmented := Rep.of (oneCocycleAugmentedRepresentation representation cycle)
  let exponentials := nilpotentLatticeAction
    (affineInfinitesimal first alpha) (affineInfinitesimal second beta)
    (affineInfinitesimal_commute first second alpha beta commute closed)
    (affineInfinitesimal_nilpotent first alpha ⟨first_cutoff + 1, first_nilpotent⟩)
    (affineInfinitesimal_nilpotent second beta ⟨second_cutoff + 1, second_nilpotent⟩)
  have equality : representationLinearEquivHom augmented = exponentials := by
    apply latticeHom_ext
    · apply LinearEquiv.ext
      intro vector
      change oneCocycleAugmentedRepresentation representation cycle radicalLatticeFirst vector =
        IsNilpotent.exp (latticeInfinitesimal
          (affineInfinitesimal first alpha) (affineInfinitesimal second beta) radicalLatticeFirst) vector
      rw [latticeInfinitesimal_first, affineInfinitesimal_exp_apply first alpha first_cutoff first_nilpotent,
        oneCocycleAugmentedRepresentation_apply, first_action, first_value]
    · apply LinearEquiv.ext
      intro vector
      change oneCocycleAugmentedRepresentation representation cycle radicalLatticeSecond vector =
        IsNilpotent.exp (latticeInfinitesimal
          (affineInfinitesimal first alpha) (affineInfinitesimal second beta) radicalLatticeSecond) vector
      rw [latticeInfinitesimal_second, affineInfinitesimal_exp_apply second beta second_cutoff second_nilpotent,
        oneCocycleAugmentedRepresentation_apply, second_action, second_value]
  apply LinearMap.ext
  intro vector
  have applied := congrArg (fun hom : RadicalLattice →* (augmented ≃ₗ[ℂ] augmented) => hom element vector) equality
  change oneCocycleAugmentedRepresentation representation cycle element vector =
    IsNilpotent.exp (latticeInfinitesimal
      (affineInfinitesimal first alpha) (affineInfinitesimal second beta) element) vector at applied
  rw [latticeInfinitesimal_affine] at applied
  exact applied

/-- A lattice cocycle in an arbitrary direction is the average of its infinitesimal value. -/
theorem latticeCocycle_direction (representation : Rep ℂ RadicalLattice)
    (cycle : groupCohomology.cocycles₁ representation)
    (first second : Module.End ℂ representation) (alpha beta : representation)
    (commute : Commute first second) (closed : first beta = second alpha)
    (first_cutoff second_cutoff : ℕ)
    (first_nilpotent : first ^ (first_cutoff + 1) = 0)
    (second_nilpotent : second ^ (second_cutoff + 1) = 0)
    (first_action : representation.ρ radicalLatticeFirst = IsNilpotent.exp first)
    (second_action : representation.ρ radicalLatticeSecond = IsNilpotent.exp second)
    (first_value : cycle radicalLatticeFirst = nilpotentExponentialAverage first (first_cutoff + 1) alpha)
    (second_value : cycle radicalLatticeSecond = nilpotentExponentialAverage second (second_cutoff + 1) beta)
    (element : RadicalLattice) (cutoff : ℕ)
    (direction_nilpotent : latticeInfinitesimal first second element ^ (cutoff + 1) = 0) :
    cycle element = nilpotentExponentialAverage (latticeInfinitesimal first second element) (cutoff + 1)
      ((element.toAdd.1 : ℂ) • alpha + (element.toAdd.2 : ℂ) • beta) := by
  have equality := latticeCocycle_augmented_exponential representation cycle first second alpha beta
    commute closed first_cutoff second_cutoff first_nilpotent second_nilpotent
    first_action second_action first_value second_value element
  have applied := congrArg (fun operator : Module.End ℂ (representation × ℂ) => (operator (0, 1)).1) equality
  rw [oneCocycleAugmentedRepresentation_apply,
    affineInfinitesimal_exp_apply _ _ cutoff direction_nilpotent] at applied
  simpa only [map_zero, one_smul, zero_add] using applied

end TernaryPeriodPolynomials.SphericalDetection.Helpers
