module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.MixedNormalization

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {N E L : Type} [Group N] [Group E] [Group L]

def splitMixedNormalize {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) :
    relativeTwoCocycles extension.inl representation :=
  cycle + relativeBoundaryOfRestriction extension.inl representation
    (splitMixedPrimitive splitting representation cycle) 0
    (splitMixedPrimitive_inl splitting representation cycle)

theorem splitMixedNormalize_val {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) :
    (splitMixedNormalize splitting representation cycle).val =
      cycle.val + twoBoundaryCycle representation (splitMixedPrimitive splitting representation cycle) := rfl

theorem splitMixedNormalize_H2 {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) :
    groupCohomology.H2π representation (splitMixedNormalize splitting representation cycle).val =
      groupCohomology.H2π representation cycle.val := by
  rw [splitMixedNormalize_val, map_add, twoBoundaryCycle_H2_zero, add_zero]

theorem splitMixedNormalize_edge {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation) (levi : L) :
    splitEdgeCycle splitting representation levi (splitMixedNormalize splitting representation cycle) =
      splitEdgeCycle splitting representation levi cycle := by
  rw [splitMixedNormalize, map_add, splitEdgeCycle_relativeBoundary, map_zero, sub_zero,
    splitMixedPrimitive_splitting]
  have boundary : oneBoundaryCycle (Rep.res extension.inl representation) (0 : representation) = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro radical
    simp only [oneBoundaryCycle_apply, map_zero, sub_self]
    rfl
  rw [boundary, sub_self, add_zero]

theorem splitMixedNormalize_mixed {extension : GroupExtension N E L} (splitting : extension.Splitting)
    (representation : Rep ℂ E) (cycle : relativeTwoCocycles extension.inl representation)
    (radical : N) (levi : L) :
    (splitMixedNormalize splitting representation cycle).val (extension.inl radical, splitting levi) = 0 := by
  change cycle.val (extension.inl radical, splitting levi) +
    twoBoundaryCycle representation (splitMixedPrimitive splitting representation cycle)
      (extension.inl radical, splitting levi) = 0
  rw [twoBoundaryCycle_apply, splitMixedPrimitive_inl, splitMixedPrimitive_splitting,
    splitMixedPrimitive_pair, map_zero]
  abel

theorem relativeTwoCocycle_radical_left_action {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation)
    (mixed : ∀ radical levi, cycle.val (extension.inl radical, splitting levi) = 0)
    (radical : N) (first second : E) :
    cycle.val (extension.inl radical * first, second) =
      representation.ρ (extension.inl radical) (cycle.val (first, second)) := by
  have equation := twoCocycle_relation representation cycle.val (extension.inl radical) first second
  rw [relativeTwoCocycle_radical_left splitting representation cycle mixed,
    relativeTwoCocycle_radical_left splitting representation cycle mixed, add_zero, add_zero] at equation
  exact equation

theorem relativeTwoCocycle_split_value {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation)
    (mixed : ∀ radical levi, cycle.val (extension.inl radical, splitting levi) = 0)
    (firstRadical transportedRadical : N) (firstLevi secondLevi : L) :
    cycle.val (extension.inl firstRadical * splitting firstLevi,
      extension.inl (splitRadicalInput splitting firstLevi transportedRadical) * splitting secondLevi) =
    representation.ρ (extension.inl firstRadical)
      (splitEdgeCycle splitting representation firstLevi cycle transportedRadical +
        representation.ρ (extension.inl transportedRadical) (cycle.val (splitting firstLevi, splitting secondLevi))) := by
  rw [relativeTwoCocycle_radical_left_action splitting representation cycle mixed]
  apply congrArg (representation.ρ (extension.inl firstRadical))
  have equation := twoCocycle_relation representation cycle.val (splitting firstLevi)
    (extension.inl (splitRadicalInput splitting firstLevi transportedRadical)) (splitting secondLevi)
  rw [mixed, map_zero, zero_add, ← splitRadicalInput_commute splitting firstLevi transportedRadical,
    relativeTwoCocycle_radical_left_action splitting representation cycle mixed] at equation
  rw [splitEdgeCycle_apply, mixed, sub_zero]
  exact equation.symm.trans (add_comm _ _)

theorem splitMixedNormalize_value {extension : GroupExtension N E L}
    (splitting : extension.Splitting) (representation : Rep ℂ E)
    (cycle : relativeTwoCocycles extension.inl representation)
    (firstRadical transportedRadical : N) (firstLevi secondLevi : L) :
    (splitMixedNormalize splitting representation cycle).val
      (extension.inl firstRadical * splitting firstLevi,
        extension.inl (splitRadicalInput splitting firstLevi transportedRadical) * splitting secondLevi) =
    representation.ρ (extension.inl firstRadical)
      (splitEdgeCycle splitting representation firstLevi cycle transportedRadical +
        representation.ρ (extension.inl transportedRadical)
          (cycle.val (splitting firstLevi, splitting secondLevi))) := by
  rw [relativeTwoCocycle_split_value splitting representation _
    (splitMixedNormalize_mixed splitting representation cycle), splitMixedNormalize_edge]
  congr 2
  apply congrArg (representation.ρ (extension.inl transportedRadical))
  change cycle.val (splitting firstLevi, splitting secondLevi) +
    twoBoundaryCycle representation (splitMixedPrimitive splitting representation cycle)
      (splitting firstLevi, splitting secondLevi) = cycle.val (splitting firstLevi, splitting secondLevi)
  rw [twoBoundaryCycle_apply, ← map_mul, splitMixedPrimitive_splitting,
    splitMixedPrimitive_splitting, splitMixedPrimitive_splitting, map_zero]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
