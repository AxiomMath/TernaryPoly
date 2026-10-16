module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicRelativeCycle
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAmbientTransportOpp

@[expose] public section


/-!
# The relative two-cocycle for the good-plane edge, opposite edge (steps 2c/2d/3, opposite edge)

Mirrors `EdgeParabolicRelativeCycle.lean`, replacing the base edge `mk gF` by the opposite edge
`mk (gF * τ)` throughout. The edge/Σ-independent pieces — `edgeParabolic_radicalU`,
`edgeParabolic_radicalU_mem`, `edgeParabolic_Cambient`, `edgeParabolic_psiG_classOf` — are reused
as-is from `EdgeParabolicRelativeCycle.lean`; only the Σ-specific pieces
(`edgeParabolic_omegaCochainOpp`, `edgeParabolic_omega_dOpp`, `edgeParabolic_omega_equivOpp`,
`edgeParabolic_cycleOpp`, `edgeParabolic_cycle_H2Opp`, `edgeParabolic_goodPlaneEdge_eqOpp`) are
mirrored, using `edgeParabolicSigmaLambdaOpp` / `edgeParabolic_sigma_conjOpp` / `edgeParabolic_radicalU_le_sigmaLambdaOpp`
(built on `EdgeParabolicAmbientTransportOpp.lean`'s Fact A-opp) in place of their base-edge
counterparts.
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
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneConj
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (goodPlaneEdgeCocycle)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot (qcls qcls_eq_zero_iff qcls_add qcls_smul)

namespace TernaryPeriodPolynomials.Argument.GoodPlaneSpan


variable {n : ℕ}

/-! ### The radical-lattice image subgroup lies in the opposite `Σ`-conjugate -/

theorem edgeParabolic_radicalU_le_sigmaLambdaOpp :
    edgeParabolic_radicalU ≤ edgeParabolicSigmaLambdaOpp := by
  rintro g ⟨p, rfl⟩
  exact edgeParabolic_factA_opp p

/-! ### Transporting the opposite-edge `primitive` into `ΛG`-coordinates -/

/-- The `gF`-conjugate of the opposite-edge ad hoc primitive, a `1`-cochain of
`edgeParabolicSigmaLambdaOpp`. -/
def edgeParabolic_omegaCochainOpp
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1) :
    cochains edgeParabolicSigmaLambdaOpp (rationalCoefficientComponent n trivialCharacter) 1 :=
  conjCochain (rationalCoefficientComponent n trivialCharacter) gF
    (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
    edgeParabolicSigmaLambdaOpp edgeParabolic_sigma_conjOpp 1 primitive

/-- **The key `hd` fact, opposite edge**: the raw boundary of the conjugated opposite-edge
primitive matches `Cambient`'s raw values everywhere. -/
theorem edgeParabolic_omega_dOpp
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C) :
    ∀ a b c, differentialOneRaw (edgeParabolic_omegaCochainOpp primitive).val ![a, b, c] =
      (edgeParabolic_Cambient C).val.val ![a, b, c] := by
  have hkey := conjCycle_boundaryMap (rationalCoefficientComponent n trivialCharacter)
    gF (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
    edgeParabolicSigmaLambdaOpp edgeParabolic_sigma_conjOpp primitive
  rw [hprimitive] at hkey
  have hval := congrArg (fun z => z.val.val) hkey
  intro a b c
  exact congrFun hval.symm ![a, b, c]

/-- **Equivariance of the conjugated opposite-edge primitive under `edgeParabolic_radicalU`.** -/
theorem edgeParabolic_omega_equivOpp
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1) :
    ∀ g ∈ edgeParabolic_radicalU, ∀ a b : RationalGL3,
      (edgeParabolic_omegaCochainOpp primitive).val ![g * a, g * b] =
        rationalCoefficientComponent n trivialCharacter g
          ((edgeParabolic_omegaCochainOpp primitive).val ![a, b]) := by
  intro g hg a b
  have hg' : g ∈ edgeParabolicSigmaLambdaOpp := edgeParabolic_radicalU_le_sigmaLambdaOpp hg
  have h := (edgeParabolic_omegaCochainOpp primitive).property ⟨g, hg'⟩ ![a, b]
  have ht : (fun i => g * (![a, b] : Fin 2 → RationalGL3) i) = ![g * a, g * b] := by
    funext i
    fin_cases i <;> rfl
  rwa [ht] at h

/-! ### The relative two-cocycle, opposite edge -/

/-- **Step 3, opposite edge**: the relative two-cocycle for `goodPlaneExtension.inl`, built from
`C`/`primitive` (opposite edge) via `relOn`. -/
def edgeParabolic_cycleOpp
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C) :
    relativeTwoCocycles goodPlaneExtension.inl (coefRep n) :=
  relOn ΛG (rationalCoefficientComponent n trivialCharacter)
    (edgeParabolic_omegaCochainOpp primitive).val (edgeParabolic_Cambient C)
    (edgeParabolic_omega_dOpp C primitive hprimitive) (U := edgeParabolic_radicalU)
    (edgeParabolic_omega_equivOpp primitive) goodPlaneExtension.inl edgeParabolic_radicalU_mem

/-- The opposite-edge relative two-cocycle has the class of `Cambient`'s ambient class. -/
theorem edgeParabolic_cycle_H2Opp
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C) :
    groupCohomology.H2π (coefRep n) (edgeParabolic_cycleOpp C primitive hprimitive).val =
      groupCohomology.H2π (coefRep n)
        (ambientCocycleToGroup ΛG (rationalCoefficientComponent n trivialCharacter)
          (edgeParabolic_Cambient C)) :=
  relOn_H2 ΛG (rationalCoefficientComponent n trivialCharacter)
    (edgeParabolic_omegaCochainOpp primitive).val (edgeParabolic_Cambient C)
    (edgeParabolic_omega_dOpp C primitive hprimitive) (U := edgeParabolic_radicalU)
    (edgeParabolic_omega_equivOpp primitive) goodPlaneExtension.inl edgeParabolic_radicalU_mem

/-! ### Step 4, opposite edge: the good-plane edge value in terms of `edgeParabolic_cycleOpp` -/

/-- **Step 4, opposite edge**: `goodPlaneEdge` of the class of `C` equals `qcls` of the edge
cocycle of the opposite-edge relative two-cocycle `edgeParabolic_cycleOpp`. -/
theorem edgeParabolic_goodPlaneEdge_eqOpp (hn : 0 < n)
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk (gF * τ) : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk (gF * τ)) (cuspFlag .plane true)
          endpoint_gF_mul_τ)
        (rationalCoefficientComponent n trivialCharacter) C) :
    goodPlaneEdge hn
        (classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C) =
      qcls (levelRep (n + 1) (-1))
        (goodPlaneEdgeCocycle (edgeParabolic_cycleOpp C primitive hprimitive)) := by
  have h1 : goodPlaneEdge hn
      (classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C) =
      goodPlaneEdgeH2 hn (psiG (n := n)
        (classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C)) :=
    rfl
  rw [h1, edgeParabolic_psiG_classOf]
  exact goodPlaneEdgeH2_apply hn (edgeParabolic_Cambient C)
    (edgeParabolic_cycleOpp C primitive hprimitive) (edgeParabolic_cycle_H2Opp C primitive hprimitive)

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
