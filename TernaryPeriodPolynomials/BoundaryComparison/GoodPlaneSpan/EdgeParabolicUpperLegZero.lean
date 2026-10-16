module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicRelativeCycle
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicLeviFactA
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneHeckeCoord

@[expose] public section


/-!
# The good-plane edge cocycle vanishes exactly at the `upper 1` Levi coordinate

Continues `EdgeParabolicRelativeCycle.lean` (step 3: the relative two-cocycle `edgeParabolic_cycle`)
and `EdgeParabolicLeviFactA.lean` (Fact A2: `edgeParabolic_factA_levi_upper`). Establishes the first
of the two legs needed for `GoodPlaneEdgeParabolic`'s target membership in
`parabolicH1 (levelRep (n + 1) (-1)) (upper 1) (lower 1)`: the edge cocycle
`goodPlaneEdgeCocycle (edgeParabolic_cycle C primitive hprimitive)` vanishes *exactly* (not just up
to `moved`) at the Levi coordinate `upper 1`, hence trivially lies in
`moved (levelRep (n + 1) (-1)) (upper 1)`.

Both terms of `GoodPlaneHeckeEdge.edgeFun` at `μ = upper 1` vanish by `relCocycleOn_vanish`: the
first because `(goodPlaneSplitting (upper 1, 1)).val ∈ edgeParabolicSigmaLambda`
(`edgeParabolic_factA_levi_upper`, via `splitting_eq`), the second because every `(UK y).val` lies
in `edgeParabolic_radicalU ≤ edgeParabolicSigmaLambda`. The common equivariance hypothesis is
`edgeParabolic_omega_equiv_sigmaLambda`, the straightforward extension of
`edgeParabolic_omega_equiv` (`EdgeParabolicRelativeCycle.lean`) from `edgeParabolic_radicalU` to all
of `edgeParabolicSigmaLambda` (dropping the restriction step, since the underlying cochain's own
`.property` is already stated for the larger group). This full vanishing of `edgeFun` propagates,
via `GoodPlaneHeckeCoord.edgeFun_eq` and extensionality of `cocycles₁`, to
`splitEdgeCycle ... = 0`, then via `edgeValLin`'s `LinearMap.comp` shape to `edgeVal ... = 0`, then
via `goodPlaneEdgeCocycle_apply` and linearity of `Phi n` to the final vanishing.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneConj
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneHeckeEdge (edgeFun inl_eq
  splitting_eq)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneHeckeCoord (edgeFun_eq)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (edgeVal edgeValLin
  goodPlaneEdgeCocycle goodPlaneEdgeCocycle_apply Phi)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


variable {n : ℕ}

/-! ### Equivariance on the full subgroup `edgeParabolicSigmaLambda` -/

/-- The conjugated primitive's equivariance, extended from `edgeParabolic_radicalU`
(`edgeParabolic_omega_equiv`) to all of `edgeParabolicSigmaLambda`: dropping the restriction step,
since `(edgeParabolic_omegaCochain primitive).property` is already stated for the full group. -/
theorem edgeParabolic_omega_equiv_sigmaLambda
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1) :
    ∀ g ∈ edgeParabolicSigmaLambda, ∀ a b : RationalGL3,
      (edgeParabolic_omegaCochain primitive).val ![g * a, g * b] =
        rationalCoefficientComponent n trivialCharacter g
          ((edgeParabolic_omegaCochain primitive).val ![a, b]) := by
  intro g hg a b
  have h := (edgeParabolic_omegaCochain primitive).property ⟨g, hg⟩ ![a, b]
  have ht : (fun i => g * (![a, b] : Fin 2 → RationalGL3) i) = ![g * a, g * b] := by
    funext i
    fin_cases i <;> rfl
  rwa [ht] at h

/-! ### The edge function vanishes at `upper 1` -/

/-- The Levi point `LK (upper 1)` lies in `edgeParabolicSigmaLambda` (Fact A2). -/
theorem edgeParabolic_LK_upper_mem_sigmaLambda :
    (LK (upper 1 : binaryArithmeticLevel)).val ∈ edgeParabolicSigmaLambda := by
  have h := edgeParabolic_factA_levi_upper
  rwa [splitting_eq] at h

/-- Every radical point `UK b` lies in `edgeParabolicSigmaLambda` (Fact A, via
`edgeParabolic_radicalU`). -/
theorem edgeParabolic_UK_mem_sigmaLambda (b : ℤ × ℤ) :
    (UK b).val ∈ edgeParabolicSigmaLambda := by
  have heq : goodPlaneExtension.inl (Multiplicative.ofAdd b) = UK b := by
    rw [inl_eq, toAdd_ofAdd]
  rw [← heq]
  exact edgeParabolic_radicalU_le_sigmaLambda (edgeParabolic_radicalU_mem _)

/-- **The key vanishing fact**: `GoodPlaneHeckeEdge.edgeFun` of `edgeParabolic_cycle`'s underlying
cocycle vanishes identically at `μ = upper 1`, for every `b`. Both terms vanish by
`relCocycleOn_vanish`, using `edgeParabolic_omega_equiv_sigmaLambda` for the equivariance and
`edgeParabolic_LK_upper_mem_sigmaLambda` / `edgeParabolic_UK_mem_sigmaLambda` for the membership. -/
theorem edgeParabolic_edgeFun_upper_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C)
    (b : ℤ × ℤ) :
    edgeFun (ρn n) (edgeParabolic_cycle C primitive hprimitive).val
        (upper 1 : binaryArithmeticLevel) b = 0 := by
  have hR : (edgeParabolic_cycle C primitive hprimitive).val =
      relCocycleOn ΛG (rationalCoefficientComponent n trivialCharacter)
        (edgeParabolic_omegaCochain primitive).val (edgeParabolic_Cambient C) := rfl
  unfold edgeFun
  rw [hR,
    relCocycleOn_vanish ΛG (rationalCoefficientComponent n trivialCharacter)
      (edgeParabolic_omegaCochain primitive).val (edgeParabolic_Cambient C)
      (edgeParabolic_omega_d C primitive hprimitive)
      (edgeParabolic_omega_equiv_sigmaLambda primitive) edgeParabolic_LK_upper_mem_sigmaLambda,
    relCocycleOn_vanish ΛG (rationalCoefficientComponent n trivialCharacter)
      (edgeParabolic_omegaCochain primitive).val (edgeParabolic_Cambient C)
      (edgeParabolic_omega_d C primitive hprimitive)
      (edgeParabolic_omega_equiv_sigmaLambda primitive) (edgeParabolic_UK_mem_sigmaLambda b)]
  abel

/-! ### Propagation to `splitEdgeCycle`, `edgeVal`, and `goodPlaneEdgeCocycle` -/

/-- The full vanishing of `edgeFun` at `upper 1` propagates to the full `splitEdgeCycle` element
(not just its value at each point), via `edgeFun_eq` and extensionality of `cocycles₁`. -/
theorem edgeParabolic_splitEdgeCycle_upper_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C) :
    splitEdgeCycle goodPlaneSplitting (coefRep n) ((upper 1 : binaryArithmeticLevel), 1)
        (edgeParabolic_cycle C primitive hprimitive) = 0 := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  have hzero := edgeParabolic_edgeFun_upper_eq_zero C primitive hprimitive
    (Multiplicative.toAdd radical)
  rw [edgeFun_eq, ofAdd_toAdd] at hzero
  exact hzero

/-- The binary coordinate `edgeVal` of `edgeParabolic_cycle` vanishes at the Levi point
`(upper 1, 1)`. -/
theorem edgeParabolic_edgeVal_upper_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C) :
    edgeVal (edgeParabolic_cycle C primitive hprimitive)
        ((upper 1 : binaryArithmeticLevel), 1) = 0 := by
  show upperRadicalCocycleCoordinate n
      (splitEdgeCycle goodPlaneSplitting (coefRep n) ((upper 1 : binaryArithmeticLevel), 1)
        (edgeParabolic_cycle C primitive hprimitive)) = 0
  rw [edgeParabolic_splitEdgeCycle_upper_eq_zero]
  exact map_zero _

/-- **Main result of this file**: the good-plane edge cocycle vanishes exactly at `upper 1`. -/
theorem edgeParabolic_goodPlaneEdgeCocycle_upper_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C) :
    (goodPlaneEdgeCocycle (edgeParabolic_cycle C primitive hprimitive)).val
        (upper 1 : binaryArithmeticLevel) = 0 := by
  rw [goodPlaneEdgeCocycle_apply, edgeParabolic_edgeVal_upper_eq_zero, map_zero]

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
