module

public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAmbientTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.CupProduct
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCore

@[expose] public section


/-!
# The relative two-cocycle for the good-plane edge, via `relOn` (steps 2c/2d/3)

Builds on `EdgeParabolicSigmaPrimitive.lean` (step 2a: `C`/`primitive` from an `InnerBoundary`
witness) and `EdgeParabolicAmbientTransport.lean` (step 2b: `edgeParabolicSigmaLambda`, Fact A).
Here we transport `C` and `primitive` by conjugation with `gF` into `ΛG`-coordinates
(`edgeParabolic_Cambient`, `edgeParabolic_omegaCochain`), establish the raw-boundary identity
`edgeParabolic_omega_d` and the `edgeParabolic_radicalU`-equivariance `edgeParabolic_omega_equiv`,
and assemble the relative two-cocycle `edgeParabolic_cycle` via `relOn`, together with its class
`edgeParabolic_cycle_H2` via `relOn_H2`. Mirrors `BadIdentPlane.lean`'s `cocycleAtGoodPlane`,
`omegaG`, `omegaG_d`, `omegaG_equiv`, `relG`, `relG_H2`, specialized to the good-plane frame `gF`
and to the smaller subgroup `edgeParabolic_radicalU` (the image of the radical lattice) rather than
`planeRad`.
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

/-! ### The radical-lattice image subgroup -/

/-- The image of the radical lattice under `goodPlaneExtension.inl`, as a subgroup of
`RationalGL3`. Mirrors `BadIdentPlane.lean`'s `planeRad` for the good-plane frame `gF`. -/
def edgeParabolic_radicalU : Subgroup RationalGL3 :=
  (ΛG.subtype.comp goodPlaneExtension.inl).range

theorem edgeParabolic_radicalU_mem (p : RadicalLattice) :
    (goodPlaneExtension.inl p).val ∈ edgeParabolic_radicalU := ⟨p, rfl⟩

theorem edgeParabolic_radicalU_le_sigmaLambda :
    edgeParabolic_radicalU ≤ edgeParabolicSigmaLambda := by
  rintro g ⟨p, rfl⟩
  exact edgeParabolic_factA p

/-! ### Transporting `C` and `primitive` into `ΛG`-coordinates -/

/-- The `gF`-conjugate of the ambient cocycle `C`, living over `ΛG`. Mirrors
`BadIdentPlane.lean`'s `cocycleAtGoodPlane`. -/
def edgeParabolic_Cambient
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter)) :
    cocycles ΛG (rationalCoefficientComponent n trivialCharacter) :=
  conjCycle (rationalCoefficientComponent n trivialCharacter) gF
    (cuspLevel .plane true) ΛG hH_conj C

/-- `psiG` identifies the class of `C` with the class of its `gF`-conjugate `Cambient`. Mirrors
`BadIdentPlane.lean`'s `psiG_cuspRes`. -/
theorem edgeParabolic_psiG_classOf
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter)) :
    psiG (n := n)
        (classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C) =
      classOf ΛG (rationalCoefficientComponent n trivialCharacter) (edgeParabolic_Cambient C) :=
  rfl

/-- The `gF`-conjugate of the ad hoc primitive, a `1`-cochain of `edgeParabolicSigmaLambda`. -/
def edgeParabolic_omegaCochain
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1) :
    cochains edgeParabolicSigmaLambda (rationalCoefficientComponent n trivialCharacter) 1 :=
  conjCochain (rationalCoefficientComponent n trivialCharacter) gF
    (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges)) edgeParabolicSigmaLambda
    edgeParabolic_sigma_conj 1 primitive

/-- **The key `hd` fact**: the raw boundary of the conjugated primitive matches `Cambient`'s raw
values everywhere. Mirrors `BadIdentPlane.lean`'s `omegaG_d`. -/
theorem edgeParabolic_omega_d
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C) :
    ∀ a b c, differentialOneRaw (edgeParabolic_omegaCochain primitive).val ![a, b, c] =
      (edgeParabolic_Cambient C).val.val ![a, b, c] := by
  have hkey := conjCycle_boundaryMap (rationalCoefficientComponent n trivialCharacter)
    gF (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges)) edgeParabolicSigmaLambda
    edgeParabolic_sigma_conj primitive
  rw [hprimitive] at hkey
  have hval := congrArg (fun z => z.val.val) hkey
  intro a b c
  exact congrFun hval.symm ![a, b, c]

/-- **Equivariance of the conjugated primitive under `edgeParabolic_radicalU`.** Follows directly
from `edgeParabolic_omegaCochain primitive`'s own membership in
`cochains edgeParabolicSigmaLambda _ 1`, restricted via `edgeParabolic_radicalU_le_sigmaLambda`. -/
theorem edgeParabolic_omega_equiv
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1) :
    ∀ g ∈ edgeParabolic_radicalU, ∀ a b : RationalGL3,
      (edgeParabolic_omegaCochain primitive).val ![g * a, g * b] =
        rationalCoefficientComponent n trivialCharacter g
          ((edgeParabolic_omegaCochain primitive).val ![a, b]) := by
  intro g hg a b
  have hg' : g ∈ edgeParabolicSigmaLambda := edgeParabolic_radicalU_le_sigmaLambda hg
  have h := (edgeParabolic_omegaCochain primitive).property ⟨g, hg'⟩ ![a, b]
  have ht : (fun i => g * (![a, b] : Fin 2 → RationalGL3) i) = ![g * a, g * b] := by
    funext i
    fin_cases i <;> rfl
  rwa [ht] at h

/-! ### The relative two-cocycle -/

/-- **Step 3**: the relative two-cocycle for `goodPlaneExtension.inl`, built from `C`/`primitive`
via `relOn`. Mirrors `BadIdentPlane.lean`'s `relG`. -/
def edgeParabolic_cycle
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C) :
    relativeTwoCocycles goodPlaneExtension.inl (coefRep n) :=
  relOn ΛG (rationalCoefficientComponent n trivialCharacter)
    (edgeParabolic_omegaCochain primitive).val (edgeParabolic_Cambient C)
    (edgeParabolic_omega_d C primitive hprimitive) (U := edgeParabolic_radicalU)
    (edgeParabolic_omega_equiv primitive) goodPlaneExtension.inl edgeParabolic_radicalU_mem

/-- The relative two-cocycle has the class of `Cambient`'s ambient class. Mirrors
`BadIdentPlane.lean`'s `relG_H2`. -/
theorem edgeParabolic_cycle_H2
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C) :
    groupCohomology.H2π (coefRep n) (edgeParabolic_cycle C primitive hprimitive).val =
      groupCohomology.H2π (coefRep n)
        (ambientCocycleToGroup ΛG (rationalCoefficientComponent n trivialCharacter)
          (edgeParabolic_Cambient C)) :=
  relOn_H2 ΛG (rationalCoefficientComponent n trivialCharacter)
    (edgeParabolic_omegaCochain primitive).val (edgeParabolic_Cambient C)
    (edgeParabolic_omega_d C primitive hprimitive) (U := edgeParabolic_radicalU)
    (edgeParabolic_omega_equiv primitive) goodPlaneExtension.inl edgeParabolic_radicalU_mem

/-! ### Step 4: the good-plane edge value, exactly, in terms of `edgeParabolic_cycle` -/

/-- **Step 4**: `goodPlaneEdge` of the class of `C` equals `qcls` of the edge cocycle of the
relative two-cocycle `edgeParabolic_cycle`. Combines `edgeParabolic_psiG_classOf` (to rewrite
`psiG` of the class of `C` as the class of `Cambient`) with `goodPlaneEdgeH2_apply` (to resolve
`goodPlaneEdgeH2` of the class of `Cambient` via the relative-cocycle machinery). -/
theorem edgeParabolic_goodPlaneEdge_eq (hn : 0 < n)
    (C : cocycles (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter))
    (primitive : cochains (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
      (rationalCoefficientComponent n trivialCharacter) 1)
    (hprimitive : boundaryMap (fixedPointLevel rationalLevel (QuotientGroup.mk gF : Edges))
        (rationalCoefficientComponent n trivialCharacter) primitive =
      subgroupRestrictionCycle
        (fixedPointLevel_edge_le_flag .plane (QuotientGroup.mk gF) (cuspFlag .plane true)
          cuspFlag_eq.symm)
        (rationalCoefficientComponent n trivialCharacter) C) :
    goodPlaneEdge hn
        (classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C) =
      qcls (levelRep (n + 1) (-1))
        (goodPlaneEdgeCocycle (edgeParabolic_cycle C primitive hprimitive)) := by
  have h1 : goodPlaneEdge hn
      (classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C) =
      goodPlaneEdgeH2 hn (psiG (n := n)
        (classOf (cuspLevel .plane true) (rationalCoefficientComponent n trivialCharacter) C)) :=
    rfl
  rw [h1, edgeParabolic_psiG_classOf]
  exact goodPlaneEdgeH2_apply hn (edgeParabolic_Cambient C)
    (edgeParabolic_cycle C primitive hprimitive) (edgeParabolic_cycle_H2 C primitive hprimitive)

end TernaryPeriodPolynomials.Argument.GoodPlaneSpan
