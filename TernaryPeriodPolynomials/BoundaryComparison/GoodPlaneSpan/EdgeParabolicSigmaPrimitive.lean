module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Helpers

@[expose] public section


/-!
# A `Σ₀`-level ad hoc primitive from an `InnerBoundary` good-plane class (step 2a)

Good-plane analogue (`.plane true`, frame `gF`) of
`Argument.CuspidalSpan.EdgeSigmaPrimitive.sigmaPrimitive_of_innerBoundary` (frame `1`) and of
`Argument.FacePairing.EdgeSigmaPrimitive.sigmaPrimitive_of_innerBoundary_goodLine` (the
line-side version). Produces, from an `InnerBoundary` witness, an explicit ambient cocycle `C` on
`cuspLevel .plane true` representing the good Shapiro coordinate, together with an ad hoc
primitive on `Σ := fixedPointLevel rationalLevel (mk gF : Edges)` whose `boundaryMap` matches `C`'s
restriction to `Σ`.
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


/-- Step 2a (good-plane side): an `InnerBoundary` plane class has an ambient cocycle
representative `C` on `cuspLevel .plane true` whose restriction to
`Σ := fixedPointLevel rationalLevel (mk gF)` is an ad hoc coboundary. -/
theorem edgeParabolic_sigmaPrimitive_of_innerBoundary {n : ℕ}
    {ξ : StratumH2 n trivialCharacter .plane}
    (inner : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter),
      classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C =
        cuspRes n trivialCharacter .plane true ξ ∧
      ∃ primitive : cochains
          (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
          (rationalCoefficientComponent n trivialCharacter) 1,
        boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
            (rationalCoefficientComponent n trivialCharacter) primitive =
          subgroupRestrictionCycle
            (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
              cuspFlag_eq.symm)
            (rationalCoefficientComponent n trivialCharacter) C := by
  have membership := innerBoundary_fixedPointH2_locallyInner inner (cuspFlag .plane true)
  have restriction :
      subgroupRestrictionH2
          (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
            cuspFlag_eq.symm)
          (rationalCoefficientComponent n trivialCharacter)
          (cuspRes n trivialCharacter .plane true ξ) = 0 :=
    (Submodule.mem_iInf
      (M := H2 (fixedPointLevel rationalLevel (cuspFlag .plane true))
        (rationalCoefficientComponent n trivialCharacter)) _).mp membership
      ⟨QuotientGroup.mk gF, cuspFlag_eq.symm⟩
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
      classOf (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter)
        (subgroupRestrictionCycle
          (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
            cuspFlag_eq.symm)
          (rationalCoefficientComponent n trivialCharacter) C) = 0 := restriction
  obtain ⟨primitive, hprimitive⟩ := (classOf_eq_zero_iff _ _ _).mp restriction2
  exact ⟨primitive, Subtype.ext hprimitive⟩

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
