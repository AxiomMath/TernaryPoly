module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyModels
public import TernaryPeriodPolynomials.Topology.Equivariant.MayerVietoris.HomologySequence

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
open CategoryTheory Limits HomologicalComplex
open IntegralGL3Congruence SingularBoundaryRestriction SymmetricSpaceBoundaryMV
open EquivariantSingularResolution EquivariantSingularSmall EquivariantSingularMayerVietoris
open EquivariantMayerVietorisHomology SymmetricSpaceBoundaryFaceAugmentation SingularCoverNaturality

/-- A commutative square can be transported across its actual comparison isomorphisms. -/
theorem conjugateSquare {C : Type*} [Category C] {X X' Y Y' A B : C}
    (i : X ≅ X') (j : Y ≅ Y') (f : X' ⟶ Y') (g : X ⟶ Y)
    (a : Y ⟶ A) (b : X ⟶ B) (c : B ⟶ A)
    (h : i.hom ≫ f=g ≫ j.hom) (k : g ≫ a=b ≫ c) :
    f ≫ j.inv ≫ a=i.inv ≫ b ≫ c := by
  apply (cancel_epi i.hom).mp
  simp only [←Category.assoc, h, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc g j.hom j.inv,j.hom_inv_id,Category.comp_id]
  exact k

def lineRetractionMap : TopCat.of UpstairsLine ⟶ TopCat.of LineFaceSum := TopCat.ofHom lineSumRetraction
def planeRetractionMap : TopCat.of UpstairsPlane ⟶ TopCat.of PlaneFaceSum := TopCat.ofHom planeSumRetraction
def interRetractionMap : TopCat.of Intersection ⟶ TopCat.of CornerFaceSum := TopCat.ofHom cornerModelEquiv.invFun

def interLeftMap : TopCat.of Intersection ⟶ TopCat.of UpstairsLine :=
  subspaceInclusion ambient Intersection UpstairsLine Set.inter_subset_left

def interRightMap : TopCat.of Intersection ⟶ TopCat.of UpstairsPlane :=
  subspaceInclusion ambient Intersection UpstairsPlane Set.inter_subset_right

theorem interLeftMap_equivariant (g : principalSix) (x : Intersection) :
    interLeftMap (g • x)=g • interLeftMap x := rfl

theorem interRightMap_equivariant (g : principalSix) (x : Intersection) :
    interRightMap (g • x)=g • interRightMap x := rfl

/-- The literal overlap-to-line square commutes up to the geometric homotopy. -/
def lineRetractionHomotopy : TopCat.Homotopy (interLeftMap ≫ lineRetractionMap)
    (interRetractionMap ≫ lineFaceMap) :=
  lineSumCompatibility.compContinuousMap intersectionHomeomorph.toHomotopyEquiv.toFun

def planeRetractionHomotopy : TopCat.Homotopy (interRightMap ≫ planeRetractionMap)
    (interRetractionMap ≫ planeFaceMap) :=
  planeSumCompatibility.compContinuousMap intersectionHomeomorph.toHomotopyEquiv.toFun

theorem lineRetraction_homology (n : ℕ) :
    homologyMap (chainMap interLeftMap interLeftMap_equivariant) n ≫
        homologyMap (chainMap lineRetractionMap lineSumRetraction_equivariant) n =
      homologyMap (chainMap interRetractionMap cornerModelEquiv_inv_equivariant) n ≫
        homologyMap lineChainMap n := by
  have h := homologyMap_homotopic (interLeftMap ≫ lineRetractionMap)
    (interRetractionMap ≫ lineFaceMap)
    (fun (g : principalSix) (x : Intersection) =>
      (congrArg lineSumRetraction (interLeftMap_equivariant g x)).trans
        (lineSumRetraction_equivariant g (interLeftMap x)))
    (fun (g : principalSix) (x : Intersection) =>
      (congrArg lineFaceMap (cornerModelEquiv_inv_equivariant g x)).trans
        (lineFaceMap_equivariant g (interRetractionMap x))) lineRetractionHomotopy n
  have ha := (congrArg (fun f => homologyMap f n)
    (EquivariantMayerVietorisHomology.chainMap_comp interLeftMap interLeftMap_equivariant
      lineRetractionMap lineSumRetraction_equivariant)).trans (homologyMap_comp _ _ n)
  have hb := (congrArg (fun f => homologyMap f n)
    (EquivariantMayerVietorisHomology.chainMap_comp interRetractionMap cornerModelEquiv_inv_equivariant
      lineFaceMap lineFaceMap_equivariant)).trans (homologyMap_comp _ _ n)
  exact ha.symm.trans (h.trans hb)

theorem planeRetraction_homology (n : ℕ) :
    homologyMap (chainMap interRightMap interRightMap_equivariant) n ≫
        homologyMap (chainMap planeRetractionMap planeSumRetraction_equivariant) n =
      homologyMap (chainMap interRetractionMap cornerModelEquiv_inv_equivariant) n ≫
        homologyMap planeChainMap n := by
  have h := homologyMap_homotopic (interRightMap ≫ planeRetractionMap)
    (interRetractionMap ≫ planeFaceMap)
    (fun (g : principalSix) (x : Intersection) =>
      (congrArg planeSumRetraction (interRightMap_equivariant g x)).trans
        (planeSumRetraction_equivariant g (interRightMap x)))
    (fun (g : principalSix) (x : Intersection) =>
      (congrArg planeFaceMap (cornerModelEquiv_inv_equivariant g x)).trans
        (planeFaceMap_equivariant g (interRetractionMap x))) planeRetractionHomotopy n
  have ha := (congrArg (fun f => homologyMap f n)
    (EquivariantMayerVietorisHomology.chainMap_comp interRightMap interRightMap_equivariant
      planeRetractionMap planeSumRetraction_equivariant)).trans (homologyMap_comp _ _ n)
  have hb := (congrArg (fun f => homologyMap f n)
    (EquivariantMayerVietorisHomology.chainMap_comp interRetractionMap cornerModelEquiv_inv_equivariant
      planeFaceMap planeFaceMap_equivariant)).trans (homologyMap_comp _ _ n)
  exact ha.symm.trans (h.trans hb)

theorem leftFaceHomology_natural (n : ℕ) :
    homologyMap (interToLeft principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant) n ≫
      (leftFaceHomologyIso n).hom = (interFaceHomologyIso n).hom ≫ homologyMap lineChainMap n := by
  have h := congrArg (fun f => homologyMap f n)
    (subspaceCorestrict_naturality principalSix ambient Intersection UpstairsLine
      intersection_invariant lineOpen_invariant (fun _ _ => rfl) (fun _ _ => rfl) Set.inter_subset_left)
  rw [homologyMap_comp,homologyMap_comp] at h
  exact conjugateSquare
    ((homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) n).mapIso interSubspaceIso)
    ((homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) n).mapIso lineSubspaceIso)
    _ _ _ _ _ h (lineRetraction_homology n)

theorem rightFaceHomology_natural (n : ℕ) :
    homologyMap (interToRight principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant) n ≫
      (rightFaceHomologyIso n).hom = (interFaceHomologyIso n).hom ≫ homologyMap planeChainMap n := by
  have h := congrArg (fun f => homologyMap f n)
    (subspaceCorestrict_naturality principalSix ambient Intersection UpstairsPlane
      intersection_invariant planeOpen_invariant (fun _ _ => rfl) (fun _ _ => rfl) Set.inter_subset_right)
  rw [homologyMap_comp,homologyMap_comp] at h
  exact conjugateSquare
    ((homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) n).mapIso interSubspaceIso)
    ((homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) n).mapIso planeSubspaceIso)
    _ _ _ _ _ h (planeRetraction_homology n)

/-- On H0, the actual subordinate-chain inclusion is exactly flag-to-line incidence. -/
theorem leftH0_natural :
    homologyMap (interToLeft principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant) 0 ≫
      leftH0Iso.hom=interH0Iso.hom ≫ lineIncidence := by
  change _ ≫ ((leftFaceHomologyIso 0).hom ≫ lineH0Iso.hom)=
    ((interFaceHomologyIso 0).hom ≫ flagH0Iso.hom) ≫ lineIncidence
  rw [←Category.assoc,leftFaceHomology_natural,Category.assoc,lineH0_natural,←Category.assoc]

theorem rightH0_natural :
    homologyMap (interToRight principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant) 0 ≫
      rightH0Iso.hom=interH0Iso.hom ≫ planeIncidence := by
  change _ ≫ ((rightFaceHomologyIso 0).hom ≫ planeH0Iso.hom)=
    ((interFaceHomologyIso 0).hom ≫ flagH0Iso.hom) ≫ planeIncidence
  rw [←Category.assoc,rightFaceHomology_natural,Category.assoc,planeH0_natural,←Category.assoc]

/-- The orientation is line minus plane, as in the actual Mayer–Vietoris chain map. -/
def incidence : flagLabels ⟶ lineLabels ⊞ planeLabels := biprod.lift lineIncidence (-planeIncidence)

def middleH0Iso : mvComplex.X₂.homology 0 ≅ lineLabels ⊞ planeLabels :=
  homologyBiprodIso leftComplex rightComplex 0 ≪≫ biprod.mapIso leftH0Iso rightH0Iso

/-- Mapping a binary lift through component isomorphisms acts on the two components. -/
theorem lift_mapIso {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {X Y Z Y' Z' : C} (a : X ⟶ Y) (b : X ⟶ Z) (e : Y ≅ Y') (f : Z ≅ Z') :
    biprod.lift a b ≫ (biprod.mapIso e f).hom=biprod.lift (a ≫ e.hom) (b ≫ f.hom) := by
  apply biprod.hom_ext <;> simp

/-- The full actual H0 Mayer–Vietoris arrow is the literal signed incidence map. -/
theorem incidence_natural : homologyMap mvComplex.f 0 ≫ middleH0Iso.hom=interH0Iso.hom ≫ incidence := by
  let H := homologyFunctor (Rep ℚ principalSix) (ComplexShape.down ℕ) 0
  let a := interToLeft principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant
  let b := interToRight principalSix ambient lineOpen planeOpen lineOpen_invariant planeOpen_invariant
  have h := biprod.map_lift_mapBiprod H leftComplex rightComplex a (-b)
  have ha : H.map a ≫ leftH0Iso.hom=interH0Iso.hom ≫ lineIncidence := leftH0_natural
  have hb : H.map (-b) ≫ rightH0Iso.hom=interH0Iso.hom ≫ (-planeIncidence) :=
    (congrArg (fun m => m ≫ rightH0Iso.hom) (H.map_neg (f := b))).trans
      ((Preadditive.neg_comp (H.map b) rightH0Iso.hom).trans
        ((congrArg Neg.neg rightH0_natural).trans (Preadditive.comp_neg _ _).symm))
  have hc : biprod.lift (interH0Iso.hom ≫ lineIncidence) (interH0Iso.hom ≫ (-planeIncidence)) =
      interH0Iso.hom ≫ incidence := by
    apply biprod.hom_ext <;> simp [incidence]
  have h2 : biprod.lift (H.map a) (H.map (-b)) ≫ (biprod.mapIso leftH0Iso rightH0Iso).hom =
      interH0Iso.hom ≫ incidence :=
    (lift_mapIso _ _ _ _).trans ((congrArg₂ biprod.lift ha hb).trans hc)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ (biprod.mapIso leftH0Iso rightH0Iso).hom) h).trans h2)

end TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
