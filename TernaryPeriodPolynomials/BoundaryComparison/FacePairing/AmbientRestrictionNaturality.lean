module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RelativeTwoCocycleNormalization

@[expose] public section


/-!
# Naturality of ambient restriction against the Mathlib comparison (M1a, KL-membership step)

`subgroupRestrictionCycle`/`subgroupRestrictionH2` (`LocalInner.lean`) restrict an *ambient*
homogeneous 2-cocycle of a larger subgroup of `RationalGL3` down to a smaller one, by literally
keeping the same underlying function `cycle.val.val` and only weakening the equivariance proof
(`subgroupRestrictionCochain`'s `toFun` is `cochain.val` verbatim). `ambientCocycleToGroup`
(`AmbientGroupH2.lean`) compares such an ambient cocycle with Mathlib's `groupCohomology.cocycles₂`
of the subgroup, again by literal evaluation (`cycle.val.val ![1, g, g*h]`,
`ambientCocycleToGroup_apply`). Both operations are therefore literal reindexings of the *same*
underlying function, so they commute with Mathlib's own restriction
(`twoCocycleRestriction`/`twoCohomologyRestriction`) along the subgroup-inclusion monoid
homomorphism `Subgroup.inclusion`, by `rfl`.

This is the naturality square, the remaining link between the ambient
restriction-vanishing fact available from an `InnerBoundary` witness
(`baseEdge_restriction_zero_of_innerBoundary` plus `goodLineRadicalInclusion_fixes_baseEdge`) and
`KL`-membership (`twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n)`
vanishing after `toH2L`).
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Ambient restriction, compared with Mathlib's `groupCohomology` via `ambientCocycleToGroup`,
agrees with Mathlib's own restriction along the subgroup-inclusion homomorphism. -/
theorem ambientCocycleToGroup_subgroupRestrictionCycle {smaller larger : Subgroup RationalGL3}
    (inclusion : smaller ≤ larger) (representation : Representation ℂ RationalGL3 V)
    (cycle : cocycles larger representation) :
    ambientCocycleToGroup smaller representation
        (subgroupRestrictionCycle inclusion representation cycle) =
      twoCocycleRestriction (Subgroup.inclusion inclusion) (subgroupCoefficientRep larger representation)
        (ambientCocycleToGroup larger representation cycle) := by
  apply Subtype.ext
  funext pair
  rfl

end TernaryPeriodPolynomials.Argument.FacePairing
