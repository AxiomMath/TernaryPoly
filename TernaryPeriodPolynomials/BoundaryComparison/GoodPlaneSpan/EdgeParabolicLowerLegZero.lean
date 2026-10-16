module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicRelativeCycleOpp
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicLeviFactAOpp
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneHeckeCoord

@[expose] public section


/-!
# The good-plane edge cocycle vanishes exactly at the `lower 1` Levi coordinate

Mirrors `EdgeParabolicUpperLegZero.lean` for the opposite edge: continues
`EdgeParabolicRelativeCycleOpp.lean` (step 3, opposite edge: the relative two-cocycle
`edgeParabolic_cycleOpp`) and `EdgeParabolicLeviFactAOpp.lean` (Fact A2-opp:
`edgeParabolic_factA_levi_lowerOpp`). Establishes the second of the two legs needed for
`GoodPlaneEdgeParabolic`'s target membership in `parabolicH1 (levelRep (n + 1) (-1)) (upper 1)
(lower 1)`: the edge cocycle `goodPlaneEdgeCocycle (edgeParabolic_cycleOpp C primitive hprimitive)`
vanishes *exactly* at the Levi coordinate `lower 1`.

Every step is the literal substitution `upper 1 ↦ lower 1`, `edgeParabolic_cycle ↦
edgeParabolic_cycleOpp`, `edgeParabolicSigmaLambda ↦ edgeParabolicSigmaLambdaOpp`,
`edgeParabolic_factA_levi_upper ↦ edgeParabolic_factA_levi_lowerOpp`,
`edgeParabolic_radicalU_le_sigmaLambda ↦ edgeParabolic_radicalU_le_sigmaLambdaOpp` applied to
`EdgeParabolicUpperLegZero.lean`'s chain: `edgeValLin`/`edgeVal` (`GoodPlaneEdge2.lean`) use the
single coordinate map `upperRadicalCocycleCoordinate n` uniformly at *every* Levi point `ℓ` (not
only at `upper 1`), and `edgeFun`/`edgeFun_eq`/`splitting_eq`/`inl_eq`/`goodPlaneEdgeCocycle_apply`
are likewise all generic in their Levi/matrix argument, so no further "opposite" analogue of any of
these is needed beyond what `EdgeParabolicRelativeCycleOpp.lean` and `EdgeParabolicLeviFactAOpp.lean`
already supply.
-/

noncomputable section

open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (lower)
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

/-! ### Equivariance on the full subgroup `edgeParabolicSigmaLambdaOpp` -/

/-- The conjugated opposite-edge primitive's equivariance, extended from `edgeParabolic_radicalU`
(`edgeParabolic_omega_equivOpp`) to all of `edgeParabolicSigmaLambdaOpp`. -/
theorem edgeParabolic_omega_equiv_sigmaLambdaOpp
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1) :
    ∀ g ∈ edgeParabolicSigmaLambdaOpp, ∀ a b : RationalGL3,
      (edgeParabolic_omegaCochainOpp primitive).val ![g * a, g * b] =
        rationalCoefficientComponent n trivialCharacter g
          ((edgeParabolic_omegaCochainOpp primitive).val ![a, b]) := by
  intro g hg a b
  have h := (edgeParabolic_omegaCochainOpp primitive).property ⟨g, hg⟩ ![a, b]
  have ht : (fun i => g * (![a, b] : Fin 2 → RationalGL3) i) = ![g * a, g * b] := by
    funext i
    fin_cases i <;> rfl
  rwa [ht] at h

/-! ### The edge function vanishes at `lower 1` -/

/-- The Levi point `LK (lower 1)` lies in `edgeParabolicSigmaLambdaOpp` (Fact A2-opp). -/
theorem edgeParabolic_LK_lower_mem_sigmaLambdaOpp :
    (LK (lower 1 : binaryArithmeticLevel)).val ∈ edgeParabolicSigmaLambdaOpp := by
  have h := edgeParabolic_factA_levi_lowerOpp
  rwa [splitting_eq] at h

/-- Every radical point `UK b` lies in `edgeParabolicSigmaLambdaOpp` (Fact A-opp, via
`edgeParabolic_radicalU`). -/
theorem edgeParabolic_UK_mem_sigmaLambdaOpp (b : ℤ × ℤ) :
    (UK b).val ∈ edgeParabolicSigmaLambdaOpp := by
  have heq : goodPlaneExtension.inl (Multiplicative.ofAdd b) = UK b := by
    rw [inl_eq, toAdd_ofAdd]
  rw [← heq]
  exact edgeParabolic_radicalU_le_sigmaLambdaOpp (edgeParabolic_radicalU_mem _)

/-- **The key vanishing fact, opposite edge**: `GoodPlaneHeckeEdge.edgeFun` of
`edgeParabolic_cycleOpp`'s underlying cocycle vanishes identically at `μ = lower 1`, for every `b`.
Both terms vanish by `relCocycleOn_vanish`, using `edgeParabolic_omega_equiv_sigmaLambdaOpp` for the
equivariance and `edgeParabolic_LK_lower_mem_sigmaLambdaOpp` / `edgeParabolic_UK_mem_sigmaLambdaOpp`
for the membership. -/
theorem edgeParabolic_edgeFun_lower_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C)
    (b : ℤ × ℤ) :
    edgeFun (ρn n) (edgeParabolic_cycleOpp C primitive hprimitive).val
        (lower 1 : binaryArithmeticLevel) b = 0 := by
  have hR : (edgeParabolic_cycleOpp C primitive hprimitive).val =
      relCocycleOn ΛG (rationalCoefficientComponent n trivialCharacter)
        (edgeParabolic_omegaCochainOpp primitive).val (edgeParabolic_Cambient C) := rfl
  unfold edgeFun
  rw [hR,
    relCocycleOn_vanish ΛG (rationalCoefficientComponent n trivialCharacter)
      (edgeParabolic_omegaCochainOpp primitive).val (edgeParabolic_Cambient C)
      (edgeParabolic_omega_dOpp C primitive hprimitive)
      (edgeParabolic_omega_equiv_sigmaLambdaOpp primitive) edgeParabolic_LK_lower_mem_sigmaLambdaOpp,
    relCocycleOn_vanish ΛG (rationalCoefficientComponent n trivialCharacter)
      (edgeParabolic_omegaCochainOpp primitive).val (edgeParabolic_Cambient C)
      (edgeParabolic_omega_dOpp C primitive hprimitive)
      (edgeParabolic_omega_equiv_sigmaLambdaOpp primitive) (edgeParabolic_UK_mem_sigmaLambdaOpp b)]
  abel

/-! ### Propagation to `splitEdgeCycle`, `edgeVal`, and `goodPlaneEdgeCocycle` -/

/-- The full vanishing of `edgeFun` at `lower 1` propagates to the full `splitEdgeCycle` element,
via `edgeFun_eq` and extensionality of `cocycles₁`. -/
theorem edgeParabolic_splitEdgeCycle_lower_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C) :
    splitEdgeCycle goodPlaneSplitting (coefRep n) ((lower 1 : binaryArithmeticLevel), 1)
        (edgeParabolic_cycleOpp C primitive hprimitive) = 0 := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  have hzero := edgeParabolic_edgeFun_lower_eq_zero C primitive hprimitive
    (Multiplicative.toAdd radical)
  rw [edgeFun_eq, ofAdd_toAdd] at hzero
  exact hzero

/-- The binary coordinate `edgeVal` of `edgeParabolic_cycleOpp` vanishes at the Levi point
`(lower 1, 1)`. -/
theorem edgeParabolic_edgeVal_lower_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C) :
    edgeVal (edgeParabolic_cycleOpp C primitive hprimitive)
        ((lower 1 : binaryArithmeticLevel), 1) = 0 := by
  show upperRadicalCocycleCoordinate n
      (splitEdgeCycle goodPlaneSplitting (coefRep n) ((lower 1 : binaryArithmeticLevel), 1)
        (edgeParabolic_cycleOpp C primitive hprimitive)) = 0
  rw [edgeParabolic_splitEdgeCycle_lower_eq_zero]
  exact map_zero _

/-- **Main result of this file**: the good-plane edge cocycle (opposite edge) vanishes exactly at
`lower 1`. -/
theorem edgeParabolic_goodPlaneEdgeCocycle_lower_eq_zero
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C) :
    (goodPlaneEdgeCocycle (edgeParabolic_cycleOpp C primitive hprimitive)).val
        (lower 1 : binaryArithmeticLevel) = 0 := by
  rw [goodPlaneEdgeCocycle_apply, edgeParabolic_edgeVal_lower_eq_zero, map_zero]

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
