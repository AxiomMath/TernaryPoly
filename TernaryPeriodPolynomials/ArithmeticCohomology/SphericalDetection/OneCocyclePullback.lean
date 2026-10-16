module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Lattice.CocycleNaturality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section


open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def oneCocyclePullbackMorphism {G H : Type} [Group G] [Group H]
    (source : Rep ℂ G) (target : Rep ℂ H) (input : H →* G)
    (comparison : source →ₗ[ℂ] target)
    (intertwines : ∀ element, (target.ρ element).comp comparison = comparison.comp (source.ρ (input element))) :
    Rep.res input source ⟶ target :=
  Rep.ofHom ⟨comparison, fun element => (intertwines element).symm⟩

theorem oneCocyclePullback_eq_mapCocycles {G H : Type} [Group G] [Group H]
    (source : Rep ℂ G) (target : Rep ℂ H) (input : H →* G)
    (comparison : source →ₗ[ℂ] target)
    (intertwines : ∀ element, (target.ρ element).comp comparison = comparison.comp (source.ρ (input element)))
    (cycle : groupCohomology.cocycles₁ source) :
    groupCohomology.mapCocycles₁ input
        (oneCocyclePullbackMorphism source target input comparison intertwines) cycle =
      oneCocyclePullback source target input comparison intertwines cycle := by
  apply groupCohomology.cocycles₁_ext
  intro element
  have equality := groupCohomology.mapCocycles₁_comp_i_apply input
    (oneCocyclePullbackMorphism source target input comparison intertwines) cycle
  exact congrFun equality element

def oneCocyclePullbackH1 {G H : Type} [Group G] [Group H]
    (source : Rep ℂ G) (target : Rep ℂ H) (input : H →* G)
    (comparison : source →ₗ[ℂ] target)
    (intertwines : ∀ element, (target.ρ element).comp comparison = comparison.comp (source.ρ (input element))) :
    groupCohomology.H1 source →ₗ[ℂ] groupCohomology.H1 target :=
  (groupCohomology.map input (oneCocyclePullbackMorphism source target input comparison intertwines) 1).hom

theorem oneCocyclePullbackH1_apply {G H : Type} [Group G] [Group H]
    (source : Rep ℂ G) (target : Rep ℂ H) (input : H →* G)
    (comparison : source →ₗ[ℂ] target)
    (intertwines : ∀ element, (target.ρ element).comp comparison = comparison.comp (source.ρ (input element)))
    (cycle : groupCohomology.cocycles₁ source) :
    oneCocyclePullbackH1 source target input comparison intertwines (groupCohomology.H1π source cycle) =
      groupCohomology.H1π target (oneCocyclePullback source target input comparison intertwines cycle) := by
  change groupCohomology.map input (oneCocyclePullbackMorphism source target input comparison intertwines) 1
    (groupCohomology.H1π source cycle) = _
  rw [groupCohomology.H1π_comp_map_apply, oneCocyclePullback_eq_mapCocycles]

theorem oneCocycle_H1_surjective {G : Type} [Group G] (representation : Rep ℂ G) :
    Function.Surjective (groupCohomology.H1π representation) := by
  intro cohomology
  induction cohomology using groupCohomology.H1_induction_on with
  | h cycle => exact ⟨cycle, rfl⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
