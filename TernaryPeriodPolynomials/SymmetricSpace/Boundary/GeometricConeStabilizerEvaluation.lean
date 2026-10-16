module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeStabilizerTotal

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open CategoryTheory Category Limits HomologicalComplex Preadditive
open IntegralGL3Congruence OrdinaryIncidence SymmetricSpaceBoundaryMV
open BoundaryFaceResolutionComparison EquivariantSingularSmall EquivariantSingularMayerVietoris

/-- Shapiro coordinates on the actual middle-face cochains. -/
def stabilizerFaceShapiroIso (W : Rep.{0} ℚ principalSix) :
    homCochains (lineStabilizerModel.complex ⊞ planeStabilizerModel.complex) W ≅
      lineStabilizerCochains W ⊞ planeStabilizerCochains W :=
  homBiprodIso lineStabilizerModel.complex planeStabilizerModel.complex W ≪≫
    biprod.mapIso (fullShapiroIso principalSix Line W) (fullShapiroIso principalSix Plane W)

section Generic
variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {A B A' B' D E : C} (l : A ⟶ A') (p : B ⟶ B') (a : A' ⟶ D) (b : B' ⟶ D) (t : D ⟶ E)

theorem conjugateDifference : biprod.map l p ≫ biprod.desc a (-b) ≫ t=
    biprod.desc (l ≫ a ≫ t) (-(p ≫ b ≫ t)) := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc,biprod.inl_desc_assoc,biprod.inl_desc]
  · simp only [biprod.inr_map_assoc,biprod.inr_desc_assoc,biprod.inr_desc,comp_neg,neg_comp]
end Generic

/-- In full Shapiro coordinates the total corner incidence is exactly line restriction minus plane restriction. -/
theorem stabilizerFaceShapiro_difference (W : Rep.{0} ℚ principalSix) :
    (stabilizerFaceShapiroIso W).inv ≫ homPullback stabilizerFaceArrow W ≫
      (fullShapiroIso principalSix Flag W).hom=stabilizerRestrictionDifference W := by
  have h := homBiprodIso_difference lineStabilizerArrow planeStabilizerArrow W
  change (biprod.map (fullShapiroIso principalSix Line W).inv (fullShapiroIso principalSix Plane W).inv ≫
    (homBiprodIso lineStabilizerModel.complex planeStabilizerModel.complex W).inv) ≫
      homPullback stabilizerFaceArrow W ≫ (fullShapiroIso principalSix Flag W).hom=_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => biprod.map (fullShapiroIso principalSix Line W).inv
      (fullShapiroIso principalSix Plane W).inv ≫ m)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun m => m ≫ (fullShapiroIso principalSix Flag W).hom) h))).trans
      (conjugateDifference _ _ _ _ _))

/-- The corner component is the actual shifted flag summand of the total cochain. -/
def stabilizerCornerComponent (W : Rep.{0} ℚ principalSix) (n : ℕ)
    (c : (stabilizerTotalCochains W).X (n+1)) : flagStabilizerModel.complex.X n ⟶ W :=
  CofiberSequence.left stabilizerFaceArrow n ≫ c

def stabilizerFaceComponent (W : Rep.{0} ℚ principalSix) (n : ℕ)
    (c : (stabilizerTotalCochains W).X n) :
    (lineStabilizerModel.complex ⊞ planeStabilizerModel.complex).X n ⟶ W :=
  (homotopyCofiber.inr stabilizerFaceArrow).f n ≫ c

def stabilizerTotalCochainAsHom (W : Rep.{0} ℚ principalSix) (n : ℕ)
    (c : (stabilizerTotalCochains W).X n) : stabilizerFaceCone.X n ⟶ W := c

/-- Literal coefficient evaluation of a total corner cochain in any actual flag-stabilizer factor. -/
theorem stabilizerCorner_evaluation (W : Rep.{0} ℚ principalSix) (n : ℕ)
    (c : (stabilizerTotalCochains W).X (n+1)) (o : labelOrbits principalSix Flag)
    (b : (Rep.barResolution ℚ (stabilizer principalSix o.out)).complex.X n) :
    (fullShapiroDegree principalSix Flag W n (stabilizerCornerComponent W n c) o).hom b=
      (stabilizerTotalCochainAsHom W (n+1) c).hom (CofiberSequence.left stabilizerFaceArrow n
        ((Family.inclusion (fun o : labelOrbits principalSix Flag => (orbitResolution principalSix o.out).complex) o).f n
          (Representation.IndV.mk (stabilizer principalSix o.out).subtype
            ((Rep.barResolution ℚ (stabilizer principalSix o.out)).complex.X n).ρ 1 b))) := rfl

/-- The induced-bar total differential retains the same negative corner coboundary. -/
theorem stabilizerTotal_d_corner_succ (W : Rep.{0} ℚ principalSix) (n : ℕ)
    (c : (stabilizerTotalCochains W).X (n+1)) :
    stabilizerCornerComponent W (n+1) ((stabilizerTotalCochains W).d (n+1) (n+2) c)=
      stabilizerFaceArrow.f (n+1) ≫ stabilizerFaceComponent W (n+1) c -
        flagStabilizerModel.complex.d (n+1) n ≫ stabilizerCornerComponent W n c := by
  change stabilizerFaceCone.X (n+1) ⟶ W at c
  have h : CofiberSequence.left stabilizerFaceArrow (n+1) ≫ stabilizerFaceCone.d (n+2) (n+1)=
      -flagStabilizerModel.complex.d (n+1) n ≫ CofiberSequence.left stabilizerFaceArrow n +
        stabilizerFaceArrow.f (n+1) ≫ (homotopyCofiber.inr stabilizerFaceArrow).f (n+1) :=
    homotopyCofiber.inlX_d stabilizerFaceArrow (n+2) (n+1) n (Cone.downRel (n+1)) (Cone.downRel n)
  change CofiberSequence.left stabilizerFaceArrow (n+1) ≫ (stabilizerFaceCone.d (n+2) (n+1) ≫ c)=_
  rw [←Category.assoc,h,add_comp,neg_comp,Category.assoc,Category.assoc]
  exact neg_add_eq_sub _ _

/-- The actual boundary-to-stabilizer map returns to geometric cochains by a specified homotopy. -/
def localBoundaryStabilizerCompatibility (W : Rep.{0} ℚ principalSix) :
    Homotopy (localBoundaryToStabilizerTotal W ≫ stabilizerTotalToGeometric W)
      (localBoundaryToFaceTotal W) := by
  have h : Homotopy
      (homPullback faceConeStabilizerEquiv.inv W ≫ homPullback faceConeStabilizerEquiv.hom W)
      (𝟙 (faceTotalCochains W)) :=
    (((linearYoneda ℚ (Rep ℚ principalSix)).obj W).rightOp.mapHomotopy
      faceConeStabilizerEquiv.homotopyHomInvId).unop
  rw [faceConeStabilizerEquiv_hom] at h
  have h' := h.compLeft (localBoundaryToFaceTotal W)
  exact (Homotopy.ofEq (Category.assoc _ _ _)).trans
    ((h'.trans (Homotopy.ofEq (Category.comp_id _))))

end TernaryPoly.SymmetricSpaceBoundaryGeometricCone
