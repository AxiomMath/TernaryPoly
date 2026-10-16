module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RelativeTwoCocycleNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SurjectiveLinearDescent

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

theorem twoCocycle_H2_surjective (representation : Rep ℂ E) :
    Function.Surjective (groupCohomology.H2π representation) := by
  intro cohomology
  induction cohomology using groupCohomology.H2_induction_on with
  | h cycle => exact ⟨cycle, rfl⟩

def relativeTwoCocycleClass (inclusion : N →* E) (representation : Rep ℂ E) :
    relativeTwoCocycles inclusion representation →ₗ[ℂ] (twoCohomologyRestriction inclusion representation).ker :=
  ((groupCohomology.H2π representation).hom.comp (relativeTwoCocycles inclusion representation).subtype).codRestrict _
    (relativeTwoCocycle_class_restriction_zero inclusion representation)

theorem relativeTwoCocycleClass_apply (inclusion : N →* E) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles inclusion representation) :
    (relativeTwoCocycleClass inclusion representation cycle).val =
      groupCohomology.H2π representation cycle.val := rfl

theorem relativeTwoCocycleClass_surjective (inclusion : N →* E) (injective : Function.Injective inclusion)
    (representation : Rep ℂ E) : Function.Surjective (relativeTwoCocycleClass inclusion representation) := by
  intro cohomology
  obtain ⟨cycle, equality⟩ := twoCocycle_H2_surjective representation cohomology.val
  have zero : groupCohomology.H2π (Rep.res inclusion representation)
      (twoCocycleRestriction inclusion representation cycle) = 0 := by
    rw [← twoCohomologyRestriction_apply, equality]
    exact cohomology.property
  obtain ⟨relative, same_class⟩ := relativeTwoCocycleRepresentative_exists inclusion injective representation cycle zero
  exact ⟨relative, Subtype.ext (same_class.trans equality)⟩

def relativeTwoCocycleEdgeClass {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    relativeTwoCocycles extension.inl representation →ₗ[ℂ]
      groupCohomology.H1 (splitRadicalH1Representation splitting representation) :=
  (groupCohomology.H1π (splitRadicalH1Representation splitting representation)).hom.comp
    (splitCocycleEdge splitting representation)

theorem relativeTwoCocycleEdgeClass_fibers {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (first second : relativeTwoCocycles extension.inl representation)
    (equality : relativeTwoCocycleClass extension.inl representation first = relativeTwoCocycleClass extension.inl representation second) :
    relativeTwoCocycleEdgeClass splitting representation first = relativeTwoCocycleEdgeClass splitting representation second :=
  splitCocycleEdge_H1_eq_of_H2_eq splitting representation first second (congrArg Subtype.val equality)

/-- The actual split-extension edge map on the kernel of radical restriction. -/
def splitCohomologyEdge {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) :
    (twoCohomologyRestriction extension.inl representation).ker →ₗ[ℂ]
      groupCohomology.H1 (splitRadicalH1Representation splitting representation) :=
  surjectiveLinearDescent
    (V := relativeTwoCocycles extension.inl representation)
    (W := (twoCohomologyRestriction extension.inl representation).ker)
    (U := groupCohomology.H1 (splitRadicalH1Representation splitting representation))
    (relativeTwoCocycleClass extension.inl representation)
    (relativeTwoCocycleClass_surjective extension.inl extension.inl_injective representation)
    (relativeTwoCocycleEdgeClass splitting representation)
    (relativeTwoCocycleEdgeClass_fibers splitting representation)

theorem splitCohomologyEdge_apply {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) :
    splitCohomologyEdge splitting representation (relativeTwoCocycleClass extension.inl representation cycle) =
      groupCohomology.H1π (splitRadicalH1Representation splitting representation)
        (splitCocycleEdge splitting representation cycle) :=
  surjectiveLinearDescent_apply (relativeTwoCocycleClass extension.inl representation)
    (relativeTwoCocycleClass_surjective extension.inl extension.inl_injective representation)
    (relativeTwoCocycleEdgeClass splitting representation)
    (relativeTwoCocycleEdgeClass_fibers splitting representation) cycle

end TernaryPeriodPolynomials.SphericalDetection.Helpers
