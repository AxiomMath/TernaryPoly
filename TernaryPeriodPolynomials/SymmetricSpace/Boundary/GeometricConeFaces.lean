module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeOpen
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Injection
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Quotient

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory Category Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryIncidenceHomology SymmetricSpaceBoundaryFaceAugmentation
open SymmetricSpaceBoundaryMV EquivariantSingularSmall EquivariantSingularMayerVietoris
open EquivariantSingularResolution EquivariantMayerVietorisHomology SingularCoverNaturality

/-- The full flag-to-line face map is the literal geometric inclusion and is injective. -/
theorem lineFaceMap_injective : Function.Injective lineFaceMap := by
  intro x y h
  apply cornerFaceSumHomeomorph.injective
  apply Subtype.ext
  have hh := congrArg (fun z => (lineFaceSumHomeomorph z).val) h
  change (lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (cornerToLine (cornerFaceSumHomeomorph x)))).val=
    (lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (cornerToLine (cornerFaceSumHomeomorph y)))).val at hh
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply] at hh
  exact hh

def lineInclusion : TopCat.of LineFaceSum ⟶ TopCat.of UpstairsLine := TopCat.ofHom lineFaceSumEquiv.toFun
def planeInclusion : TopCat.of PlaneFaceSum ⟶ TopCat.of UpstairsPlane := TopCat.ofHom planeFaceSumEquiv.toFun
def flagInclusion : TopCat.of CornerFaceSum ⟶ TopCat.of Intersection := TopCat.ofHom cornerModelEquiv.toFun

/-- Full-face inclusions commute strictly with the actual intersection inclusions. -/
theorem lineInclusion_square : lineFaceMap ≫ lineInclusion=flagInclusion ≫ interLeftMap := by
  ext x : 1
  apply Subtype.ext
  change (lineFaceSumHomeomorph (lineFaceSumHomeomorph.symm (cornerToLine (cornerFaceSumHomeomorph x)))).val=_
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem planeInclusion_square : planeFaceMap ≫ planeInclusion=flagInclusion ≫ interRightMap := by
  ext x : 1
  apply Subtype.ext
  change (planeFaceSumHomeomorph (planeFaceSumHomeomorph.symm (cornerToPlane (cornerFaceSumHomeomorph x)))).val=_
  rw [Homeomorph.apply_symm_apply]
  rfl

def lineToOpen : lineChains ⟶ leftComplex :=
  chainMap lineInclusion lineFaceSumEquiv_equivariant ≫ lineSubspaceIso.hom

def planeToOpen : planeChains ⟶ rightComplex :=
  chainMap planeInclusion planeFaceSumEquiv_equivariant ≫ planeSubspaceIso.hom

def flagToOpen : flagChains ⟶ interComplex :=
  chainMap flagInclusion cornerModelEquiv_equivariant ≫ interSubspaceIso.hom

/-- The signed full-family face-chain arrow retains the exact line-minus-plane convention. -/
def faceArrow : flagChains ⟶ lineChains ⊞ planeChains := biprod.lift lineChainMap (-planeChainMap)

/-- The comparison to the middle open-chain complex is the pair of actual face inclusions. -/
def facesToOpen : lineChains ⊞ planeChains ⟶ mvComplex.X₂ := biprod.map lineToOpen planeToOpen

theorem chainMap_eq {G : Type} [Group G] {E F : TopCat.{0}}
    [MulAction G E] [ContinuousConstSMul G E] [MulAction G F] [ContinuousConstSMul G F]
    (f g : E ⟶ F) (hf : ∀ (a : G) x,f (a • x)=a • f x)
    (hg : ∀ (a : G) x,g (a • x)=a • g x) (h : f=g) : chainMap f hf=chainMap g hg := by
  subst g
  rfl

theorem lineChainInclusion_square : lineChainMap ≫ chainMap lineInclusion lineFaceSumEquiv_equivariant=
    chainMap flagInclusion cornerModelEquiv_equivariant ≫ chainMap interLeftMap interLeftMap_equivariant :=
  (chainMap_comp lineFaceMap lineFaceMap_equivariant lineInclusion lineFaceSumEquiv_equivariant).symm.trans
    ((chainMap_eq _ _ _ _ lineInclusion_square).trans
      (chainMap_comp flagInclusion cornerModelEquiv_equivariant interLeftMap interLeftMap_equivariant))

theorem planeChainInclusion_square : planeChainMap ≫ chainMap planeInclusion planeFaceSumEquiv_equivariant=
    chainMap flagInclusion cornerModelEquiv_equivariant ≫ chainMap interRightMap interRightMap_equivariant :=
  (chainMap_comp planeFaceMap planeFaceMap_equivariant planeInclusion planeFaceSumEquiv_equivariant).symm.trans
    ((chainMap_eq _ _ _ _ planeInclusion_square).trans
      (chainMap_comp flagInclusion cornerModelEquiv_equivariant interRightMap interRightMap_equivariant))

theorem lineToOpen_square : lineChainMap ≫ lineToOpen=
    flagToOpen ≫ interToLeft principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant := by
  have h : interSubspaceIso.hom ≫ interToLeft principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant=
      chainMap interLeftMap interLeftMap_equivariant ≫ lineSubspaceIso.hom :=
    subspaceCorestrict_naturality principalSix ambient Intersection UpstairsLine
      intersection_invariant lineOpen_invariant (fun _ _ => rfl) (fun _ _ => rfl) Set.inter_subset_left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ lineSubspaceIso.hom) lineChainInclusion_square).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => chainMap flagInclusion cornerModelEquiv_equivariant ≫ m) h.symm).trans
          (Category.assoc _ _ _).symm)))

theorem planeToOpen_square : planeChainMap ≫ planeToOpen=
    flagToOpen ≫ interToRight principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant := by
  have h : interSubspaceIso.hom ≫ interToRight principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant=
      chainMap interRightMap interRightMap_equivariant ≫ planeSubspaceIso.hom :=
    subspaceCorestrict_naturality principalSix ambient Intersection UpstairsPlane
      intersection_invariant planeOpen_invariant (fun _ _ => rfl) (fun _ _ => rfl) Set.inter_subset_right
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ planeSubspaceIso.hom) planeChainInclusion_square).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => chainMap flagInclusion cornerModelEquiv_equivariant ≫ m) h.symm).trans
          (Category.assoc _ _ _).symm)))

/-- The entire signed face diagram maps strictly into the actual open-cover diagram. -/
theorem faceArrow_square : flagToOpen ≫ mvComplex.f=faceArrow ≫ facesToOpen := by
  apply biprod.hom_ext
  · change (flagToOpen ≫ biprod.lift _ _) ≫ biprod.fst=
      (biprod.lift lineChainMap (-planeChainMap) ≫ biprod.map lineToOpen planeToOpen) ≫ biprod.fst
    simp only [Category.assoc,biprod.lift_fst,biprod.map_fst,biprod.lift_fst_assoc]
    exact lineToOpen_square.symm
  · change (flagToOpen ≫ biprod.lift _ _) ≫ biprod.snd=
      (biprod.lift lineChainMap (-planeChainMap) ≫ biprod.map lineToOpen planeToOpen) ≫ biprod.snd
    simp only [Category.assoc,biprod.lift_snd,biprod.map_snd,biprod.lift_snd_assoc,
      Preadditive.comp_neg,Preadditive.neg_comp]
    exact congrArg Neg.neg planeToOpen_square.symm

/-- The actual face inclusion induces exactly the inverse of the face-homology comparison. -/
theorem lineToOpen_homology (n : ℕ) : homologyMap lineToOpen n=(leftFaceHomologyIso n).inv :=
  homologyMap_comp _ _ n

theorem planeToOpen_homology (n : ℕ) : homologyMap planeToOpen n=(rightFaceHomologyIso n).inv :=
  homologyMap_comp _ _ n

theorem flagToOpen_homology (n : ℕ) : homologyMap flagToOpen n=(interFaceHomologyIso n).inv :=
  homologyMap_comp _ _ n

instance lineToOpen_quasiIso : QuasiIso lineToOpen := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,lineToOpen_homology]
  infer_instance
instance planeToOpen_quasiIso : QuasiIso planeToOpen := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,planeToOpen_homology]
  infer_instance
instance flagToOpen_quasiIso : QuasiIso flagToOpen := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,flagToOpen_homology]
  infer_instance

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
