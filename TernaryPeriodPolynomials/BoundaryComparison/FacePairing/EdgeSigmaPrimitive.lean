module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RadicalFactorization
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineHecke

@[expose] public section


/-!
# A `Σ`-level ad hoc primitive from an `InnerBoundary` good-line class (M1a, step 2a)

Mirrors `Argument.CuspidalSpan.EdgeSigmaPrimitive`'s plane-side
`sigmaPrimitive_of_innerBoundary` (and the first half of this file's own
`KLMembership.fixedPointH2_mem_KL_of_innerBoundary`): for `coordinate` with an `InnerBoundary`
witness, we produce an explicit ambient cocycle `C : cocycles Λ₁ (ρn n)` representing
`fixedPointH2 rationalLevel (ρn n) (mk rationalGoodLine) coordinate`, together with an ad hoc
primitive on `Σ := fixedPointLevel rationalLevel (mk baseEdge)` whose `boundaryMap` matches `C`'s
restriction to `Σ`. This stops short of `fixedPointH2_mem_KL_of_innerBoundary`'s Mathlib-level
`H2`-vanishing conclusion, keeping the witnesses `C`/`primitive` available for the good-line edge
class's parabolicity argument (`GoodLineEdgeParabolic.lean`), which needs an explicit relative
two-cocycle representative, not merely the fact that its class lies in `KL n`.
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

/-- **Step 2a (good-line side).** An `InnerBoundary` `.line`-side class has an ambient cocycle
representative `C` on `Λ₁` whose restriction to `Σ := fixedPointLevel rationalLevel (mk baseEdge)`
is an ad hoc coboundary. -/
theorem sigmaPrimitive_of_innerBoundary_goodLine {n : ℕ}
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate) :
    ∃ C : cocycles Λ₁ (ρn n),
      classOf Λ₁ (ρn n) C =
        fixedPointH2 rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
          coordinate ∧
      ∃ primitive : cochains
          (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n) 1,
        boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n)
            primitive =
          subgroupRestrictionCycle innerInclusion (ρn n) C := by
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
  refine ⟨C, hx.symm, ?_⟩
  have restriction2 :
      classOf (fixedPointLevel rationalLevel (QuotientGroup.mk baseEdge : Edges)) (ρn n)
        (subgroupRestrictionCycle innerInclusion (ρn n) C) = 0 := restriction
  obtain ⟨primitive, hprimitive⟩ := (classOf_eq_zero_iff _ _ _).mp restriction2
  exact ⟨primitive, Subtype.ext hprimitive⟩

end TernaryPeriodPolynomials.Argument.FacePairing
