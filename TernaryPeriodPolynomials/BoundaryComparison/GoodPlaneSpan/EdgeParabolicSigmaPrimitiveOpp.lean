module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicSwapOpp
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Helpers

@[expose] public section


/-!
# A `Σopp`-level ad hoc primitive from an `InnerBoundary` good-plane class (step 2a, opposite edge)

Mirrors `EdgeParabolicSigmaPrimitive.lean`'s `edgeParabolic_sigmaPrimitive_of_innerBoundary`,
replacing the edge `mk gF` by the opposite edge `mk (gF * τ)` (`EdgeParabolicSwapOpp.lean`), using
`endpoint_gF_mul_τ` in place of `cuspFlag_eq.symm` to instantiate the same
`innerBoundary_fixedPointH2_locallyInner` witness at this different index of the `iInf`. The
resulting cocycle `C` need not literally coincide with the upper-leg file's `C`: both represent the
same class `cuspRes n trivialCharacter .plane true ξ` (via each file's own `hx`), which is all the
final assembly needs to relate both legs to the single value `goodPlaneEdge hn (cuspRes ... ξ)`.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


/-- Step 2a (good-plane side, opposite edge): an `InnerBoundary` plane class has an ambient
cocycle representative `C` on `cuspLevel .plane true` whose restriction to
`Σopp := fixedPointLevel rationalLevel (mk (gF * τ))` is an ad hoc coboundary. -/
theorem edgeParabolic_sigmaPrimitive_of_innerBoundaryOpp {n : ℕ}
    {ξ : StratumH2 n trivialCharacter .plane}
    (inner : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter),
      classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C =
        cuspRes n trivialCharacter .plane true ξ ∧
      ∃ primitive : cochains
          (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
          (rationalCoefficientComponent n trivialCharacter) 1,
        boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
            (rationalCoefficientComponent n trivialCharacter) primitive =
          subgroupRestrictionCycle
            (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
              endpoint_gF_mul_τ)
            (rationalCoefficientComponent n trivialCharacter) C := by
  have membership := innerBoundary_fixedPointH2_locallyInner inner (cuspFlag .plane true)
  have restriction :
      subgroupRestrictionH2
          (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
            endpoint_gF_mul_τ)
          (rationalCoefficientComponent n trivialCharacter)
          (cuspRes n trivialCharacter .plane true ξ) = 0 :=
    (Submodule.mem_iInf
      (M := H2 (fixedPointLevel rationalLevel (cuspFlag .plane true))
        (rationalCoefficientComponent n trivialCharacter)) _).mp membership
      ⟨QuotientGroup.mk (gF * τ), endpoint_gF_mul_τ⟩
  obtain ⟨representative, hrep, -⟩ := inner
  set C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) :=
    fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (cuspFlag .plane true) representative with hC
  have hx : cuspRes n trivialCharacter .plane true ξ =
      classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C := by
    rw [hC, ← hrep]
    exact fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (cuspFlag .plane true) representative
  rw [hx] at restriction
  refine ⟨C, hx.symm, ?_⟩
  have restriction2 :
      classOf (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter)
        (subgroupRestrictionCycle
          (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
            endpoint_gF_mul_τ)
          (rationalCoefficientComponent n trivialCharacter) C) = 0 := restriction
  obtain ⟨primitive, hprimitive⟩ := (classOf_eq_zero_iff _ _ _).mp restriction2
  exact ⟨primitive, Subtype.ext hprimitive⟩

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
