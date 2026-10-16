module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleDirections

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

attribute [local instance] complexEndRationalAlgebra

theorem nilpotentAverage_intertwines {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (source : Module.End ℂ V) (target : Module.End ℂ W)
    (comparison : V →ₗ[ℂ] W) (intertwines : target.comp comparison = comparison.comp source)
    (cutoff : ℕ) (vector : V) :
    nilpotentExponentialAverage target cutoff (comparison vector) =
      comparison (nilpotentExponentialAverage source cutoff vector) := by
  simp only [nilpotentExponentialAverage, LinearMap.sum_apply, rationalEnd_smul_apply,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro power _
  have equality := Module.End.commute_pow_left_of_commute intertwines power
  exact congrArg (fun operator : V →ₗ[ℂ] W =>
    (↑((↑(power + 1).factorial : ℚ)⁻¹) : ℂ) • operator vector) equality

theorem intertwining_power_zero {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (source : Module.End ℂ V) (target : Module.End ℂ W)
    (comparison : V →ₗ[ℂ] W) (injective : Function.Injective comparison)
    (intertwines : target.comp comparison = comparison.comp source)
    (power : ℕ) (nilpotent : target ^ power = 0) : source ^ power = 0 := by
  apply LinearMap.ext
  intro vector
  apply injective
  have equality := Module.End.commute_pow_left_of_commute intertwines power
  have applied := congrArg (fun operator : V →ₗ[ℂ] W => operator vector) equality
  rw [nilpotent, LinearMap.zero_comp, LinearMap.zero_apply, LinearMap.comp_apply] at applied
  simpa only [LinearMap.zero_apply, map_zero] using applied.symm

def oneCocyclePullback {G H : Type} [Group G] [Group H]
    (source : Rep ℂ G) (target : Rep ℂ H) (input : H →* G)
    (comparison : source →ₗ[ℂ] target)
    (intertwines : ∀ element, (target.ρ element).comp comparison = comparison.comp (source.ρ (input element))) :
    groupCohomology.cocycles₁ source →ₗ[ℂ] groupCohomology.cocycles₁ target where
  toFun cycle := ⟨fun element => comparison (cycle (input element)), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    rw [map_mul, oneCocycle_mul, map_add]
    have equality := congrArg (fun operator : source →ₗ[ℂ] target => operator (cycle (input second)))
      (intertwines first)
    change target.ρ first (comparison (cycle (input second))) =
      comparison (source.ρ (input first) (cycle (input second))) at equality
    rw [equality]⟩
  map_add' first second := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_add comparison (first (input element)) (second (input element))
  map_smul' scalar cycle := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_smul comparison scalar (cycle (input element))

theorem oneCocyclePullback_apply {G H : Type} [Group G] [Group H]
    (source : Rep ℂ G) (target : Rep ℂ H) (input : H →* G)
    (comparison : source →ₗ[ℂ] target)
    (intertwines : ∀ element, (target.ρ element).comp comparison = comparison.comp (source.ρ (input element)))
    (cycle : groupCohomology.cocycles₁ source) (element : H) :
    oneCocyclePullback source target input comparison intertwines cycle element =
      comparison (cycle (input element)) := rfl

/-- Inverse averaging is natural under a change of lattice direction and an injective intertwiner. -/
theorem latticeCocycle_direction_natural (representation : Rep ℂ RadicalLattice)
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
    {W : Type*} [AddCommGroup W] [Module ℂ W] (target : Module.End ℂ W)
    (comparison : representation →ₗ[ℂ] W) (injective : Function.Injective comparison)
    (element : RadicalLattice)
    (intertwines : target.comp comparison = comparison.comp (latticeInfinitesimal first second element))
    (cutoff : ℕ) (target_nilpotent : target ^ (cutoff + 1) = 0) :
    (nilpotentAverageEquiv target ⟨cutoff + 1, target_nilpotent⟩ cutoff).symm
        (comparison (cycle element)) =
      comparison ((element.toAdd.1 : ℂ) • alpha + (element.toAdd.2 : ℂ) • beta) := by
  have direction_nilpotent := intertwining_power_zero _ target comparison injective intertwines
    (cutoff + 1) target_nilpotent
  rw [latticeCocycle_direction representation cycle first second alpha beta commute closed
    first_cutoff second_cutoff first_nilpotent second_nilpotent first_action second_action
    first_value second_value element cutoff direction_nilpotent,
    ← nilpotentAverage_intertwines _ target comparison intertwines]
  exact (nilpotentAverageEquiv target ⟨cutoff + 1, target_nilpotent⟩ cutoff).symm_apply_apply _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
