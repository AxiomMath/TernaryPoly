module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Comparison
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.FaceCone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.NerveLabels
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConePsi
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.StratumQuasi
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.CapHomotopic

@[expose] public section


/-!
# The carrier-respecting comparison of the model cone with the library's face cone

`exists_PsiF`: there is a chain map `Ψ_F' : coneR ⟶ faceCone` (model cone of the three nerve resolutions to the cone of
the equivariant singular chains of the three face sums) which is a quasi-isomorphism, compatible with the
augmentations, and whose cap product with every cocycle `c` of the face cone agrees with the cap product of `Ψ_F' ≫ c`
up to a homotopy (`CapSystem.Homotopic`).  It is built by acyclic carriers: the carrier of a cell with label `z`
is the sub-complex of simplices carrying the face(s) `z` (`FaceCarriers`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology
open GeneralEisenstein
open TernaryPoly.OrdinaryIncidence TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.SymmetricSpaceBoundaryFaces TernaryPoly.SymmetricSpaceBoundaryMV
  TernaryPoly.SingularBoundaryRestriction
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

attribute [local instance] Comparison.vertexAction

open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

attribute [local instance] CapCompat.lineLabelTopology CapCompat.planeLabelTopology CapCompat.flagLabelTopology
  CapCompat.lineLabelDiscrete CapCompat.planeLabelDiscrete CapCompat.flagLabelDiscrete

theorem flagStratum_quasiIso (w : resFlag.complex ⟶ flagChains)
    (hc : ∀ s : (nerveCells Γ6 RationalGL3 Flag Comparison.vertexAction_free').S 0,
      (w.f 0).hom ((nerveCells Γ6 RationalGL3 Flag Comparison.vertexAction_free').cell 0 s) ∈
        flagFaceK (nerveLab Γ6 RationalGL3 Flag Comparison.vertexAction_free' 0 s) 0)
    (he : ∀ x, (singEps (G := principalSix) (TopCat.of CornerFaceSum)).hom ((w.f 0).hom x) =
      (nerveEps Γ6 RationalGL3 Flag).hom x) : QuasiIso w :=
  sigma_stratum_quasiIso flagFamily flagLabel_equivariant RationalGL3 Comparison.vertexAction_free' 1 w hc he

theorem lineStratum_quasiIso (w : resLine.complex ⟶ lineChains)
    (hc : ∀ s : (nerveCells Γ6 RationalGL3 Line Comparison.vertexAction_free').S 0,
      (w.f 0).hom ((nerveCells Γ6 RationalGL3 Line Comparison.vertexAction_free').cell 0 s) ∈
        lineFaceK (nerveLab Γ6 RationalGL3 Line Comparison.vertexAction_free' 0 s) 0)
    (he : ∀ x, (singEps (G := principalSix) (TopCat.of LineFaceSum)).hom ((w.f 0).hom x) =
      (nerveEps Γ6 RationalGL3 Line).hom x) : QuasiIso w :=
  sigma_stratum_quasiIso lineFamily lineLabel_equivariant RationalGL3 Comparison.vertexAction_free' 1 w hc he

theorem planeStratum_quasiIso (w : resPlane.complex ⟶ planeChains)
    (hc : ∀ s : (nerveCells Γ6 RationalGL3 Plane Comparison.vertexAction_free').S 0,
      (w.f 0).hom ((nerveCells Γ6 RationalGL3 Plane Comparison.vertexAction_free').cell 0 s) ∈
        planeFaceK (nerveLab Γ6 RationalGL3 Plane Comparison.vertexAction_free' 0 s) 0)
    (he : ∀ x, (singEps (G := principalSix) (TopCat.of PlaneFaceSum)).hom ((w.f 0).hom x) =
      (nerveEps Γ6 RationalGL3 Plane).hom x) : QuasiIso w :=
  sigma_stratum_quasiIso planeFamily planeLabel_equivariant RationalGL3 Comparison.vertexAction_free' 1 w hc he

/-- Labels of the model cone. -/
def modelLabels := nerveLabels Γ6 RationalGL3 Flag Line Plane Comparison.vertexAction_free'
  SymmetricSpaceBoundaryFaceAugmentation.flagLine flagLine_equivariant
  SymmetricSpaceBoundaryFaceAugmentation.flagPlane flagPlane_equivariant

theorem model_strict : PushCone.Strict (a := flagLineHom.hom) (b := flagPlaneHom.hom)
    (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) :=
  nerve_strict Γ6 RationalGL3 Flag Line Plane
    SymmetricSpaceBoundaryFaceAugmentation.flagLine flagLine_equivariant
    SymmetricSpaceBoundaryFaceAugmentation.flagPlane flagPlane_equivariant

theorem model_diag : modelLabels.Diag (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) :=
  nerveLabels_diag Γ6 RationalGL3 Flag Line Plane Comparison.vertexAction_free'
    SymmetricSpaceBoundaryFaceAugmentation.flagLine flagLine_equivariant
    SymmetricSpaceBoundaryFaceAugmentation.flagPlane flagPlane_equivariant

/-- The existence of a carried quasi-isomorphism `coneR ⟶ faceCone` (cap compatibility is proved below). -/
theorem exists_PsiF_carried : ∃ u : coneR ⟶ SymmetricSpaceBoundaryGeometricCone.faceCone,
    (∀ n, (PushCone.pushCarrierData (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
      (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets).Carried (u.f n)) ∧
    u.f 0 ≫ (pushConeOfCofiber lineChainMap planeChainMap).eps FaceCone.SL FaceCone.SP =
      (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom).eps (nerveDiagSystem Γ6 RationalGL3 Line)
        (nerveDiagSystem Γ6 RationalGL3 Plane) ∧ QuasiIso u :=
  exists_pushPsi flagLineHom.hom flagPlaneHom.hom lineChainMap planeChainMap modelLabels FaceCone.targets
    (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) FaceCone.SA FaceCone.SL FaceCone.SP model_strict FaceCone.strict
    FaceCone.good
    (fun _ => nerveEps_single Γ6 RationalGL3 Line _)
    (fun _ => nerveEps_single Γ6 RationalGL3 Plane _)
    (fun w hc he => flagStratum_quasiIso w (hc 0) he)
    (fun w hc he => lineStratum_quasiIso w (hc 0) he)
    (fun w hc he => planeStratum_quasiIso w (hc 0) he)

/-- The model diagonal system on the cone `coneR`. -/
def modelDiagSystem : DiagSystem coneR :=
  pushConeDiagSystem flagLineHom.hom flagPlaneHom.hom (nerveDiagSystem Γ6 RationalGL3 Flag)
    (nerveDiagSystem Γ6 RationalGL3 Line) (nerveDiagSystem Γ6 RationalGL3 Plane) model_strict

/-- The diagonal system of the library's face cone. -/
def faceDiagSystem : DiagSystem SymmetricSpaceBoundaryGeometricCone.faceCone :=
  pushConeDiagSystem lineChainMap planeChainMap FaceCone.SA FaceCone.SL FaceCone.SP FaceCone.strict

/-- **The carrier-respecting comparison `Ψ_F' : coneR ⟶ faceCone`**: a quasi-isomorphism compatible with the
augmentations, whose cap with every cocycle `c` of the face cone is homotopic to the cap of `u ≫ c`. -/
theorem exists_PsiF : ∃ u : coneR ⟶ SymmetricSpaceBoundaryGeometricCone.faceCone, QuasiIso u ∧
    u.f 0 ≫ faceDiagSystem.eps = modelDiagSystem.eps ∧
    ∀ {W : Rep.{0} ℚ Γ6} {n : ℕ} (c : SymmetricSpaceBoundaryGeometricCone.faceCone.X n ⟶ W)
      (hc : SymmetricSpaceBoundaryGeometricCone.faceCone.d (n+1) n ≫ c = 0),
      CapSystem.Homotopic modelDiagSystem.toCapSystem faceDiagSystem.toCapSystem u c hc := by
  obtain ⟨u, hu, hueps, hq⟩ := exists_PsiF_carried
  exact ⟨u, hq, hueps, fun c hc => PushCone.pushCone_cap_compat (pushConeOfCofiber flagLineHom.hom flagPlaneHom.hom)
    (pushConeOfCofiber lineChainMap planeChainMap) modelLabels FaceCone.targets
    (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) FaceCone.SA FaceCone.SL FaceCone.SP model_strict FaceCone.strict
    FaceCone.good model_diag FaceCone.respects_flag FaceCone.respects_line FaceCone.respects_plane
    u hu hueps c hc⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
