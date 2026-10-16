module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeTotal

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory Category Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryIncidenceHomology SymmetricSpaceBoundaryFaceAugmentation SymmetricSpaceBoundaryMV
open EquivariantSingularSmall EquivariantSingularMayerVietoris EquivariantSingularResolution
open EquivariantMayerVietorisHomology SingularCoverNaturality

/-- The actual full line-face inclusion into the entire boundary. -/
def lineToBoundary : TopCat.of LineFaceSum ⟶ ambient := lineInclusion ≫ leftInclusionMap
/-- The actual full plane-face inclusion into the entire boundary. -/
def planeToBoundary : TopCat.of PlaneFaceSum ⟶ ambient := planeInclusion ≫ rightInclusionMap

theorem lineToBoundary_equivariant (g : principalSix) (x : LineFaceSum) :
    lineToBoundary (g • x)=g • lineToBoundary x := by
  change leftInclusionMap (lineInclusion (g • x))=g • leftInclusionMap (lineInclusion x)
  rw [show lineInclusion (g • x)=g • lineInclusion x from lineFaceSumEquiv_equivariant g x]
  rfl

theorem planeToBoundary_equivariant (g : principalSix) (x : PlaneFaceSum) :
    planeToBoundary (g • x)=g • planeToBoundary x := by
  change rightInclusionMap (planeInclusion (g • x))=g • rightInclusionMap (planeInclusion x)
  rw [show planeInclusion (g • x)=g • planeInclusion x from planeFaceSumEquiv_equivariant g x]
  rfl

def lineChainToBoundary : lineChains ⟶ boundaryChains := chainMap lineToBoundary lineToBoundary_equivariant
def planeChainToBoundary : planeChains ⟶ boundaryChains := chainMap planeToBoundary planeToBoundary_equivariant

theorem lineOpen_to_boundary : lineToOpen ≫
    leftToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover ≫
      smallEquiv.hom=lineChainToBoundary := by
  exact (congrArg (fun m => lineToOpen ≫ m) left_chain_ambient).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => chainMap lineInclusion lineFaceSumEquiv_equivariant ≫ m)
        (Iso.hom_inv_id_assoc lineSubspaceIso (chainMap leftInclusionMap leftInclusionMap_equivariant))).trans
          (chainMap_comp lineInclusion lineFaceSumEquiv_equivariant leftInclusionMap leftInclusionMap_equivariant).symm))

theorem planeOpen_to_boundary : planeToOpen ≫
    rightToCover principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant opens_cover ≫
      smallEquiv.hom=planeChainToBoundary := by
  exact (congrArg (fun m => planeToOpen ≫ m) right_chain_ambient).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => chainMap planeInclusion planeFaceSumEquiv_equivariant ≫ m)
        (Iso.hom_inv_id_assoc planeSubspaceIso (chainMap rightInclusionMap rightInclusionMap_equivariant))).trans
          (chainMap_comp planeInclusion planeFaceSumEquiv_equivariant rightInclusionMap rightInclusionMap_equivariant).symm))

/-- The full-face comparison is literally the pair of geometric face restrictions. -/
theorem fullFace_boundary_map : facesToOpen ≫ mvComplex.g ≫ smallEquiv.hom=
    biprod.desc lineChainToBoundary planeChainToBoundary := by
  apply biprod.hom_ext'
  · change biprod.inl ≫ biprod.map lineToOpen planeToOpen ≫ biprod.desc _ _ ≫ smallEquiv.hom=_
    simp only [biprod.inl_map_assoc,biprod.inl_desc_assoc,biprod.inl_desc]
    exact lineOpen_to_boundary
  · change biprod.inr ≫ biprod.map lineToOpen planeToOpen ≫ biprod.desc _ _ ≫ smallEquiv.hom=_
    simp only [biprod.inr_map_assoc,biprod.inr_desc_assoc,biprod.inr_desc]
    exact planeOpen_to_boundary

/-- Pullback of the full-family total comparison preserves both genuine geometric restriction maps. -/
theorem boundaryToFaceTotal_geometric_restriction (W : Rep.{0} ℚ principalSix) :
    boundaryToFaceTotal W ≫ homPullback (homotopyCofiber.inr faceArrow) W ≫
      (homBiprodIso lineChains planeChains W).hom=
        biprod.lift (homPullback lineChainToBoundary W) (homPullback planeChainToBoundary W) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ (homBiprodIso lineChains planeChains W).hom)
      ((boundaryToFaceTotal_restriction W).trans (congrArg (fun m => homPullback m W) fullFace_boundary_map))).trans
        (homBiprodIso_restriction lineChainToBoundary planeChainToBoundary W))

/-- The cochain incidence is precisely restriction to flags from lines minus restriction from planes. -/
theorem face_restriction_difference (W : Rep.{0} ℚ principalSix) :
    (homBiprodIso lineChains planeChains W).inv ≫ homPullback faceArrow W=
      biprod.desc (homPullback lineChainMap W) (-homPullback planeChainMap W) :=
  homBiprodIso_difference lineChainMap planeChainMap W

def cornerInclusion (n : ℕ) : flagChains.X n ⟶ faceCone.X (n+1) :=
  homotopyCofiber.inlX faceArrow n (n+1) (BoundaryFaceResolutionComparison.Cone.downRel n)

def middleInclusion (n : ℕ) : (lineChains ⊞ planeChains).X n ⟶ faceCone.X n :=
  (homotopyCofiber.inr faceArrow).f n

def faceComponent (W : Rep.{0} ℚ principalSix) (n : ℕ) (c : (faceTotalCochains W).X n) :
    (lineChains ⊞ planeChains).X n ⟶ W := middleInclusion n ≫ c

def cornerComponent (W : Rep.{0} ℚ principalSix) (n : ℕ) (c : (faceTotalCochains W).X (n+1)) :
    flagChains.X n ⟶ W := cornerInclusion n ≫ c

/-- On the face component the total differential is the ordinary cochain differential. -/
theorem total_d_face (W : Rep.{0} ℚ principalSix) (n : ℕ) (c : (faceTotalCochains W).X n) :
    faceComponent W (n+1) ((faceTotalCochains W).d n (n+1) c)=
      (lineChains ⊞ planeChains).d (n+1) n ≫ faceComponent W n c :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ c) (homotopyCofiber.inrX_d faceArrow (n+1) n)).trans (Category.assoc _ _ _))

/-- At degree zero the corner differential is exactly the signed face restriction. -/
theorem total_d_corner_zero (W : Rep.{0} ℚ principalSix) (c : (faceTotalCochains W).X 0) :
    cornerComponent W 0 ((faceTotalCochains W).d 0 1 c)=faceArrow.f 0 ≫ faceComponent W 0 c :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ c) (homotopyCofiber.inlX_d' faceArrow 1 0
      (BoundaryFaceResolutionComparison.Cone.downRel 0) (by simp [ComplexShape.down_Rel]))).trans (Category.assoc _ _ _))

/-- In every positive degree the corner differential is signed face restriction minus the corner coboundary. -/
theorem total_d_corner_succ (W : Rep.{0} ℚ principalSix) (n : ℕ) (c : (faceTotalCochains W).X (n+1)) :
    cornerComponent W (n+1) ((faceTotalCochains W).d (n+1) (n+2) c)=
      faceArrow.f (n+1) ≫ faceComponent W (n+1) c - flagChains.d (n+1) n ≫ cornerComponent W n c := by
  change faceCone.X (n+1) ⟶ W at c
  have h : cornerInclusion (n+1) ≫ faceCone.d (n+2) (n+1)=
      -flagChains.d (n+1) n ≫ cornerInclusion n + faceArrow.f (n+1) ≫ middleInclusion (n+1) :=
    homotopyCofiber.inlX_d faceArrow (n+2) (n+1) n
      (BoundaryFaceResolutionComparison.Cone.downRel (n+1)) (BoundaryFaceResolutionComparison.Cone.downRel n)
  change cornerInclusion (n+1) ≫ (faceCone.d (n+2) (n+1) ≫ c)=_
  rw [←Category.assoc,h,Preadditive.add_comp,Preadditive.neg_comp,Category.assoc,Category.assoc]
  exact neg_add_eq_sub _ _

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
