module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RadicalFactorization
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RestrictionComposition
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.AmbientRestrictionNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineHecke

@[expose] public section


/-!
# An `InnerBoundary` line class's good-line restriction lies in `KL` (M1a, KL-membership step)

For `coordinate` a `.line`-side stratum class with an `InnerBoundary` witness, the direct
restriction `fixedPointH2 rationalLevel (ρn n) (mk rationalGoodLine) coordinate` to the good-line
stabilizer `Λ₁` lies in `KL n` (`GoodLineHecke.lean`), the classes whose restriction to the
`baseEdge`-radical vanishes after passing to group cohomology.

**Route.** `innerBoundary_fixedPointH2_locallyInner` (`LocalInner.lean`) places that restriction
directly in `locallyInnerClasses n trivialCharacter .line (mk rationalGoodLine)`, an infimum of
`subgroupRestrictionH2`-kernels over every edge whose line-side endpoint is the good line.
Instantiating that infimum at `baseEdge` (via `baseEdge_line_eq_goodLine`) gives vanishing of
`subgroupRestrictionH2 (fixedPointLevel_edge_le_flag ...) (ρn n)`. Since `Λ₁` is definitionally
`flagArithmeticStabilizer .line (mk rationalGoodLine) = fixedPointLevel rationalLevel (mk
rationalGoodLine)` (both unfold to `rationalLevel ⊓ MulAction.stabilizer RationalGL3 (mk
rationalGoodLine)`), that inclusion proof and `innerInclusion` (`RadicalFactorization.lean`) are
two proofs of the *same* `Prop`, hence definitionally equal by proof irrelevance: no cast lemma is
needed to read the vanishing fact directly against `innerInclusion`.

From there: identify the restricted class as `classOf Λ₁ (ρn n) C` for the ambient cycle `C`
underlying the `InnerBoundary` witness (`fixedPointH2_classOf`); push the vanishing fact through
`subgroupRestrictionH2_classOf` (new, by the same `mapQ`-unfolds-on-`classOf` pattern as
`fixedPointH2_classOf`) and `classOf_eq_zero_iff` to a coboundary witness; and transport that
witness to `KL`-membership by factoring `goodLineRadicalInclusion` through `innerInclusion`
(`goodLineRadicalInclusion_eq_inclusion_comp_radicalToSmaller`), composing restrictions
(`twoCohomologyRestriction_comp`, `twoCohomologyRestriction_apply`), and comparing ambient
restriction with Mathlib's own (`ambientCocycleToGroup_subgroupRestrictionCycle`) before closing
with `ambientCocycle_H2_zero_iff`.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.GoodLineHecke

namespace TernaryPeriodPolynomials.Argument.FacePairing


variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- `subgroupRestrictionH2` commutes with the `classOf` quotient map, exactly as
`fixedPointH2_classOf` does for `fixedPointH2`: both are `Submodule.mapQ` applied to a
cocycle-level map that only weakens an equivariance proof, leaving the underlying cochain function
untouched. -/
theorem subgroupRestrictionH2_classOf {smaller larger : Subgroup RationalGL3}
    (inclusion : smaller ≤ larger) (representation : Representation ℂ RationalGL3 V)
    (cycle : cocycles larger representation) :
    subgroupRestrictionH2 inclusion representation (classOf larger representation cycle) =
      classOf smaller representation (subgroupRestrictionCycle inclusion representation cycle) :=
  rfl

/-- **KL-membership.** The good-line restriction of an `InnerBoundary` `.line`-side class lies in
`KL n`. -/
theorem fixedPointH2_mem_KL_of_innerBoundary {n : ℕ}
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate) :
    fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
        coordinate ∈ KL n := by
  have membership :=
    innerBoundary_fixedPointH2_locallyInner inner (QuotientGroup.mk rationalGoodLine : Flags .line)
  have restriction :
      subgroupRestrictionH2 innerInclusion (ρn n)
          (fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
            coordinate) = 0 :=
    (Submodule.mem_iInf
      (M := H2 (fixedPointLevel rationalLevel (QuotientGroup.mk rationalGoodLine : Flags .line))
        (ρn n)) _).mp membership ⟨QuotientGroup.mk baseEdge, baseEdge_line_eq_goodLine⟩
  obtain ⟨representative, hrep, -⟩ := inner
  set C : cocycles Λ₁ (ρn n) :=
    fixedPointCycle rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
      representative with hC
  have hx : fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
        coordinate = classOf Λ₁ (ρn n) C := by
    rw [hC, ← hrep]
    exact fixedPointH2_classOf rationalLevel (ρn n)
      (QuotientGroup.mk rationalGoodLine : Flags .line) representative
  rw [hx] at restriction
  have restriction2 :
      classOf (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n)
        (subgroupRestrictionCycle innerInclusion (ρn n) C) = 0 := restriction
  have hzero := (classOf_eq_zero_iff _ _ _).mp restriction2
  show twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n)
      (toH2L n (fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
        coordinate)) = 0
  rw [hx, toH2L_classOf, goodLineRadicalInclusion_eq_inclusion_comp_radicalToSmaller,
    twoCohomologyRestriction_comp]






  show twoCohomologyRestriction radicalToSmaller
      (Rep.res (Subgroup.inclusion innerInclusion) (subgroupCoefficientRep Λ₁ (ρn n)))
      (twoCohomologyRestriction (Subgroup.inclusion innerInclusion) (subgroupCoefficientRep Λ₁ (ρn n))
        (groupCohomology.H2π (subgroupCoefficientRep Λ₁ (ρn n)) (ambientCocycleToGroup Λ₁ (ρn n) C))) = 0
  rw [twoCohomologyRestriction_apply, ← ambientCocycleToGroup_subgroupRestrictionCycle]
  show twoCohomologyRestriction radicalToSmaller
      (subgroupCoefficientRep (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n))
      (groupCohomology.H2π
        (subgroupCoefficientRep (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n))
        (ambientCocycleToGroup (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n)
          (subgroupRestrictionCycle innerInclusion (ρn n) C))) = 0
  have hinner :
      groupCohomology.H2π
          (subgroupCoefficientRep
            (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n))
          (ambientCocycleToGroup
            (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n)
            (subgroupRestrictionCycle innerInclusion (ρn n) C)) = 0 :=
    (ambientCocycle_H2_zero_iff _ _ _).mpr hzero
  rw [hinner, map_zero]

end TernaryPeriodPolynomials.Argument.FacePairing
