module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.CanonFull
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FaceCoords

@[expose] public section


/-!
# Face-component agreement: the model's face coordinates are the library's restrictions to the open faces

Formalized by Claude Sonnet 5.5.

The face components of a class of `H^n(∂M; W)` in the model are the line and plane components `homPullback coneLine`,
`homPullback conePlane` of the model cone, applied after `(modelBoundary_cohomology_iso W n).inv`.  The library's restrictions to
the open faces are `localBoundaryToFaceTotal` followed by the pullback along the inclusions `lineFaceIncl`, `planeFaceIncl` of the
face chains into the face cone.  `faceLine_eq_original`, `facePlane_eq_original`: for every `W`, every degree `n` and
every class, the model's face component equals the library's restriction followed by the comparison `lineModelCmp`,
`planeModelCmp` of the face-chain resolutions with the model resolutions.  The proof is the homotopy `lineModelHomotopy`
between `coneLine ≫ uCone ≫ e⁻¹` and `lineModelCmp ≫ lineFaceIncl` (uniqueness of maps between resolutions over the augmentation,
`lineStratumHomotopy`, and `faceConeStabilizerEquiv`).
-/

open CategoryTheory Category Limits HomologicalComplex
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryGeometricCone TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.IntegralGL3Congruence
open TernaryPoly.EquivariantSingularSmall
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

/-- The inclusion of the line-face chains into the library's face cone. -/
def lineFaceIncl : lineChains ⟶ faceCone := biprod.inl ≫ homotopyCofiber.inr faceArrow

def planeFaceIncl : planeChains ⟶ faceCone := biprod.inr ≫ homotopyCofiber.inr faceArrow

def lineStabIncl : lineStabilizerModel.complex ⟶ stabilizerFaceCone :=
  biprod.inl ≫ homotopyCofiber.inr stabilizerFaceArrow

def planeStabIncl : planeStabilizerModel.complex ⟶ stabilizerFaceCone :=
  biprod.inr ≫ homotopyCofiber.inr stabilizerFaceArrow

theorem lineFaceIncl_stab : lineFaceIncl ≫ faceConeToStabilizer =
    lineStabilizerComparison.hom ≫ lineStabIncl := by
  unfold lineFaceIncl lineStabIncl
  rw [Category.assoc, faceConeToStabilizer_inr, ← Category.assoc, ← Category.assoc]
  congr 1
  exact biprod.inl_map _ _

theorem planeFaceIncl_stab : planeFaceIncl ≫ faceConeToStabilizer =
    planeStabilizerComparison.hom ≫ planeStabIncl := by
  unfold planeFaceIncl planeStabIncl
  rw [Category.assoc, faceConeToStabilizer_inr, ← Category.assoc, ← Category.assoc]
  congr 1
  exact biprod.inr_map _ _

theorem inr_uCone : homotopyCofiber.inr (SymmetricSpaceBoundaryFull.signedArrow flagLineHom.hom flagPlaneHom.hom) ≫
    uCone = biprod.map (comparison resLine lineStabilizerModel).hom (comparison resPlane planeStabilizerModel).hom ≫
      homotopyCofiber.inr stabilizerFaceArrow :=
  CofiberSequence.inr_comparisonMap _ _ _ _ _

theorem coneLine_uCone : coneLine ≫ uCone = (comparison resLine lineStabilizerModel).hom ≫ lineStabIncl := by
  have h := inr_uCone
  calc coneLine ≫ uCone = biprod.inl ≫ (homotopyCofiber.inr (SymmetricSpaceBoundaryFull.signedArrow flagLineHom.hom
        flagPlaneHom.hom) ≫ uCone) := by simp only [coneLine, Category.assoc]
    _ = biprod.inl ≫ (biprod.map (comparison resLine lineStabilizerModel).hom
        (comparison resPlane planeStabilizerModel).hom ≫ homotopyCofiber.inr stabilizerFaceArrow) := by rw [h]
    _ = _ := by rw [← Category.assoc, biprod.inl_map, Category.assoc]; rfl

theorem conePlane_uCone : conePlane ≫ uCone = (comparison resPlane planeStabilizerModel).hom ≫ planeStabIncl := by
  have h := inr_uCone
  calc conePlane ≫ uCone = biprod.inr ≫ (homotopyCofiber.inr (SymmetricSpaceBoundaryFull.signedArrow flagLineHom.hom
        flagPlaneHom.hom) ≫ uCone) := by simp only [conePlane, Category.assoc]
    _ = biprod.inr ≫ (biprod.map (comparison resLine lineStabilizerModel).hom
        (comparison resPlane planeStabilizerModel).hom ≫ homotopyCofiber.inr stabilizerFaceArrow) := by rw [h]
    _ = _ := by rw [← Category.assoc, biprod.inr_map, Category.assoc]; rfl

theorem comparison_f_zero_pi {Z : Rep.{0} ℚ principalSix} (R R' : ProjectiveResolution Z) :
    (comparison R R').hom.f 0 ≫ R'.π.f 0 = R.π.f 0 :=
  congrArg (fun m => m.f 0) (comparison_augmentation R R')

/-- The stratum map `resLine → lineStabilizerModel` of `uCone` is homotopic to the composite of the two resolution
comparisons `resLine → lineResolution → lineStabilizerModel`. -/
def lineStratumHomotopy :
    Homotopy (comparison resLine lineStabilizerModel).hom
      ((comparison resLine lineResolution).hom ≫ lineStabilizerComparison.hom) := by
  have : ∀ n, Projective (resLine.complex.X n) := fun n => resLine.projective n
  refine uniqHomotopy (Q := lineStabilizerModel) _ _ ?_
  rw [comparison_f_zero_pi]
  change _ = ((comparison resLine lineResolution).hom.f 0 ≫ (comparison lineResolution lineStabilizerModel).hom.f 0)
    ≫ _
  rw [Category.assoc, comparison_f_zero_pi, comparison_f_zero_pi]

def planeStratumHomotopy :
    Homotopy (comparison resPlane planeStabilizerModel).hom
      ((comparison resPlane planeResolution).hom ≫ planeStabilizerComparison.hom) := by
  have : ∀ n, Projective (resPlane.complex.X n) := fun n => resPlane.projective n
  refine uniqHomotopy (Q := planeStabilizerModel) _ _ ?_
  rw [comparison_f_zero_pi]
  change _ = ((comparison resPlane planeResolution).hom.f 0 ≫ (comparison planeResolution planeStabilizerModel).hom.f 0)
    ≫ _
  rw [Category.assoc, comparison_f_zero_pi, comparison_f_zero_pi]

/-- `jF ≃ lineStabCmp ≫ jS ≫ e⁻¹`. -/
def lineInclHomotopy : Homotopy lineFaceIncl
    (lineStabilizerComparison.hom ≫ lineStabIncl ≫ faceConeStabilizerEquiv.inv) := by
  have h1 : Homotopy lineFaceIncl (lineFaceIncl ≫ (faceConeStabilizerEquiv.hom ≫ faceConeStabilizerEquiv.inv)) :=
    (Homotopy.ofEq (Category.comp_id _).symm).trans
      ((faceConeStabilizerEquiv.homotopyHomInvId.symm).compLeft lineFaceIncl)
  have hf : lineFaceIncl ≫ faceConeStabilizerEquiv.hom = lineStabilizerComparison.hom ≫ lineStabIncl := by
    rw [faceConeStabilizerEquiv_hom]; exact lineFaceIncl_stab
  refine h1.trans (Homotopy.ofEq ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ faceConeStabilizerEquiv.inv) hf).trans
    (Category.assoc _ _ _))

def planeInclHomotopy : Homotopy planeFaceIncl
    (planeStabilizerComparison.hom ≫ planeStabIncl ≫ faceConeStabilizerEquiv.inv) := by
  have h1 : Homotopy planeFaceIncl (planeFaceIncl ≫ (faceConeStabilizerEquiv.hom ≫ faceConeStabilizerEquiv.inv)) :=
    (Homotopy.ofEq (Category.comp_id _).symm).trans
      ((faceConeStabilizerEquiv.homotopyHomInvId.symm).compLeft planeFaceIncl)
  have hf : planeFaceIncl ≫ faceConeStabilizerEquiv.hom = planeStabilizerComparison.hom ≫ planeStabIncl := by
    rw [faceConeStabilizerEquiv_hom]; exact planeFaceIncl_stab
  refine h1.trans (Homotopy.ofEq ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ faceConeStabilizerEquiv.inv) hf).trans
    (Category.assoc _ _ _))

/-- **The model line inclusion is the library's line-face inclusion, up to homotopy**:
`coneLine ≫ uCone ≫ e⁻¹ ≃ (resLine → lineResolution) ≫ lineFaceIncl`. -/
def lineModelHomotopy : Homotopy (coneLine ≫ uCone ≫ faceConeStabilizerEquiv.inv)
    ((comparison resLine lineResolution).hom ≫ lineFaceIncl) := by
  have e1 : coneLine ≫ uCone ≫ faceConeStabilizerEquiv.inv =
      (comparison resLine lineStabilizerModel).hom ≫ lineStabIncl ≫ faceConeStabilizerEquiv.inv := by
    rw [← Category.assoc, coneLine_uCone, Category.assoc]
  refine (Homotopy.ofEq e1).trans ?_
  refine ((lineStratumHomotopy.compRight (lineStabIncl ≫ faceConeStabilizerEquiv.inv)).trans
    (Homotopy.ofEq (Category.assoc _ _ _))).trans ?_
  refine Homotopy.trans ?_ ((lineInclHomotopy.compLeft (comparison resLine lineResolution).hom).symm.trans
    (Homotopy.ofEq rfl))
  exact Homotopy.ofEq rfl

def planeModelHomotopy : Homotopy (conePlane ≫ uCone ≫ faceConeStabilizerEquiv.inv)
    ((comparison resPlane planeResolution).hom ≫ planeFaceIncl) := by
  have e1 : conePlane ≫ uCone ≫ faceConeStabilizerEquiv.inv =
      (comparison resPlane planeStabilizerModel).hom ≫ planeStabIncl ≫ faceConeStabilizerEquiv.inv := by
    rw [← Category.assoc, conePlane_uCone, Category.assoc]
  refine (Homotopy.ofEq e1).trans ?_
  refine ((planeStratumHomotopy.compRight (planeStabIncl ≫ faceConeStabilizerEquiv.inv)).trans
    (Homotopy.ofEq (Category.assoc _ _ _))).trans ?_
  refine Homotopy.trans ?_ ((planeInclHomotopy.compLeft (comparison resPlane planeResolution).hom).symm.trans
    (Homotopy.ofEq rfl))
  exact Homotopy.ofEq rfl

/-- The comparison of the model line resolution with the chains of the line face sum. -/
def lineModelCmp : resLine.complex ⟶ lineChains := (comparison resLine lineResolution).hom

def planeModelCmp : resPlane.complex ⟶ planeChains := (comparison resPlane planeResolution).hom

/-- The library's restriction of a class of `H^*(∂M; W)` to the line faces (the chains of the line face sum). -/
def subLineRestr (W : Rep.{0} ℚ principalSix) : localBoundaryCochains W ⟶ homCochains lineChains W :=
  localBoundaryToFaceTotal W ≫ homPullback lineFaceIncl W

def subPlaneRestr (W : Rep.{0} ℚ principalSix) : localBoundaryCochains W ⟶ homCochains planeChains W :=
  localBoundaryToFaceTotal W ≫ homPullback planeFaceIncl W

/-- **Face-component agreement, line faces** (all degrees, all coefficient systems, all classes): the model's line
coordinate `H(coneLine^*) ∘ (modelBoundary_cohomology_iso)⁻¹` of a class of `H^n(∂M; W)` is the library's restriction to the
line faces followed by the comparison of the line-face chains `lineResolution` with the model resolution `resLine`. -/
theorem faceLine_eq_original (W : Rep.{0} ℚ principalSix) (n : ℕ) :
    homologyMap (modelBoundaryQuasiIso W) n ≫ homologyMap (homPullback coneLine W) n =
      homologyMap (subLineRestr W) n ≫ homologyMap (homPullback lineModelCmp W) n := by
  have h1 : modelBoundaryQuasiIso W ≫ homPullback coneLine W =
      localBoundaryToFaceTotal W ≫ homPullback (coneLine ≫ uCone ≫ faceConeStabilizerEquiv.inv) W := by
    unfold modelBoundaryQuasiIso localBoundaryToStabilizerTotal
    rw [coneEquiv_hom_eq, homPullback_comp, homPullback_comp, Category.assoc, Category.assoc, Category.assoc]
  have h2 : subLineRestr W ≫ homPullback lineModelCmp W =
      localBoundaryToFaceTotal W ≫ homPullback (lineModelCmp ≫ lineFaceIncl) W := by
    unfold subLineRestr
    rw [homPullback_comp, Category.assoc]
  rw [← homologyMap_comp, ← homologyMap_comp, h1, h2]
  exact ((TernaryPoly.EquivariantSingularPairHomotopy.homPullbackHomotopy lineModelHomotopy W).compLeft
    (localBoundaryToFaceTotal W)).homologyMap_eq n

theorem facePlane_eq_original (W : Rep.{0} ℚ principalSix) (n : ℕ) :
    homologyMap (modelBoundaryQuasiIso W) n ≫ homologyMap (homPullback conePlane W) n =
      homologyMap (subPlaneRestr W) n ≫ homologyMap (homPullback planeModelCmp W) n := by
  have h1 : modelBoundaryQuasiIso W ≫ homPullback conePlane W =
      localBoundaryToFaceTotal W ≫ homPullback (conePlane ≫ uCone ≫ faceConeStabilizerEquiv.inv) W := by
    unfold modelBoundaryQuasiIso localBoundaryToStabilizerTotal
    rw [coneEquiv_hom_eq, homPullback_comp, homPullback_comp, Category.assoc, Category.assoc, Category.assoc]
  have h2 : subPlaneRestr W ≫ homPullback planeModelCmp W =
      localBoundaryToFaceTotal W ≫ homPullback (planeModelCmp ≫ planeFaceIncl) W := by
    unfold subPlaneRestr
    rw [homPullback_comp, Category.assoc]
  rw [← homologyMap_comp, ← homologyMap_comp, h1, h2]
  exact ((TernaryPoly.EquivariantSingularPairHomotopy.homPullbackHomotopy planeModelHomotopy W).compLeft
    (localBoundaryToFaceTotal W)).homologyMap_eq n

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
