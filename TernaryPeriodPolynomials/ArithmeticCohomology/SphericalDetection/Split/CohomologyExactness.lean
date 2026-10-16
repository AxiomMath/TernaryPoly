module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CocycleDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleUnits

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

def splitRelativeInflatedCocycle {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation))
    (unit_zero : cycle (1, 1) = 0) : relativeTwoCocycles extension.inl representation :=
  ⟨splitInflatedCocycle splitting representation cycle, by
    intro first second
    rw [splitInflatedCocycle_apply, extension.rightHom_inl, extension.rightHom_inl, unit_zero]
    rfl⟩

theorem splitRelativeInflatedCocycle_edge_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation))
    (unit_zero : cycle (1, 1) = 0) (levi : L) :
    splitEdgeCycle splitting representation levi (splitRelativeInflatedCocycle splitting representation cycle unit_zero) = 0 := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  change splitInflatedCocycle splitting representation cycle
      (splitting levi, extension.inl (splitRadicalInput splitting levi radical)) -
    splitInflatedCocycle splitting representation cycle (extension.inl radical, splitting levi) = 0
  rw [splitInflatedCocycle_apply, splitInflatedCocycle_apply, extension.rightHom_inl,
    extension.rightHom_inl, splitting.rightHom_splitting, twoCocycle_one_left, twoCocycle_one_right, unit_zero, map_zero]
  exact sub_self _

theorem splitRelativeInflatedCocycle_edge_class_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : groupCohomology.cocycles₂ (splitInvariantRepresentation splitting representation))
    (unit_zero : cycle (1, 1) = 0) :
    splitCocycleEdge splitting representation (splitRelativeInflatedCocycle splitting representation cycle unit_zero) = 0 := by
  apply groupCohomology.cocycles₁_ext
  intro levi
  rw [splitCocycleEdge_apply, splitRelativeInflatedCocycle_edge_zero, map_zero]
  rfl

theorem splitInvariantInflation_restriction_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cohomology : groupCohomology.H2 (splitInvariantRepresentation splitting representation)) :
    twoCohomologyRestriction extension.inl representation (splitInvariantInflation splitting representation cohomology) = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (splitInvariantRepresentation splitting representation) cohomology
  rw [← unitNormalizedTwoCocycle_H2, splitInvariantInflation_apply]
  exact relativeTwoCocycle_class_restriction_zero extension.inl representation
    (splitRelativeInflatedCocycle splitting representation (unitNormalizedTwoCocycle _ cycle) (unitNormalizedTwoCocycle_unit _ cycle))

def splitInvariantInflationKernel {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    groupCohomology.H2 (splitInvariantRepresentation splitting representation) →ₗ[ℂ]
      (twoCohomologyRestriction extension.inl representation).ker :=
  (splitInvariantInflation splitting representation).codRestrict _ (splitInvariantInflation_restriction_zero splitting representation)

theorem splitInvariantInflationKernel_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cohomology : groupCohomology.H2 (splitInvariantRepresentation splitting representation)) :
    (splitInvariantInflationKernel splitting representation cohomology).val =
      splitInvariantInflation splitting representation cohomology := rfl

theorem splitInvariantInflationKernel_edge_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cohomology : groupCohomology.H2 (splitInvariantRepresentation splitting representation)) :
    splitCohomologyEdge splitting representation (splitInvariantInflationKernel splitting representation cohomology) = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (splitInvariantRepresentation splitting representation) cohomology
  let normalized := unitNormalizedTwoCocycle (splitInvariantRepresentation splitting representation) cycle
  let relative := splitRelativeInflatedCocycle splitting representation normalized (unitNormalizedTwoCocycle_unit _ cycle)
  have equality : splitInvariantInflationKernel splitting representation
      (groupCohomology.H2π (splitInvariantRepresentation splitting representation) cycle) =
      relativeTwoCocycleClass extension.inl representation relative := by
    apply Subtype.ext
    change splitInvariantInflation splitting representation (groupCohomology.H2π _ cycle) =
      groupCohomology.H2π representation (splitInflatedCocycle splitting representation normalized)
    rw [← splitInvariantInflation_apply, unitNormalizedTwoCocycle_H2]
  rw [equality, splitCohomologyEdge_apply, splitRelativeInflatedCocycle_edge_class_zero, map_zero]

/-- Exactness at the radical-restriction kernel: the edge kernel is the image of invariant inflation. -/
theorem splitCohomologyEdge_exact {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    (splitInvariantInflationKernel splitting representation).range = (splitCohomologyEdge splitting representation).ker := by
  apply Submodule.ext
  intro cohomology
  constructor
  · rintro ⟨levi_class, rfl⟩
    exact splitInvariantInflationKernel_edge_zero splitting representation levi_class
  · intro zero
    obtain ⟨levi_class, equality⟩ := splitCohomologyEdge_kernel_inflation splitting representation cohomology zero
    exact ⟨levi_class, Subtype.ext equality⟩

theorem splitCohomologyEdge_injective_of_invariant_H2_zero {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E)
    (vanishing : ∀ cohomology : groupCohomology.H2 (splitInvariantRepresentation splitting representation), cohomology = 0) :
    Function.Injective (splitCohomologyEdge splitting representation) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro cohomology zero
  obtain ⟨levi_class, equality⟩ := splitCohomologyEdge_kernel_inflation splitting representation cohomology zero
  apply Subtype.ext
  change cohomology.val = 0
  rw [← equality, vanishing levi_class, map_zero]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
