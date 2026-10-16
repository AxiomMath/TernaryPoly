module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConeCorner
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Restriction
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullCofiberNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex BoundaryFaceResolutionComparison
open SymmetricSpaceBoundaryFullTransfer

variable {G : Type} [Group G] (H : Subgroup G)
  {A B : ChainComplex (Rep.{0} ℚ G) ℕ} (f : A ⟶ B) (W : Rep.{0} ℚ G) (a : A.X 0 ⟶ W)

/-- The canonical restriction/cofiber isomorphism preserves the literal augmented corner. -/
theorem coneRestriction_cornerCochain :
    (homotopyCofiber.mapHomologicalComplexObjIso f (Rep.resFunctor H.subtype)).inv.f 1 ≫
      (Rep.resFunctor H.subtype).map (coneCornerCochain f W a) =
        coneCornerCochain (((Rep.resFunctor H.subtype).mapHomologicalComplex
          (ComplexShape.down ℕ)).map f) (Rep.res H.subtype W) ((Rep.resFunctor H.subtype).map a) := by
  let F := Rep.resFunctor H.subtype (k := ℚ)
  let f' := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map f
  apply homotopyCofiber.ext_from_X f' 0 1 (Cone.downRel 0)
  · change homotopyCofiber.inlX f' 0 1 (Cone.downRel 0) ≫
      ((homotopyCofiber.mapHomologicalComplexObjXIso f F 1).inv ≫
        F.map (CofiberSequence.first f 0 ≫ a)) =
      homotopyCofiber.inlX f' 0 1 (Cone.downRel 0) ≫ (CofiberSequence.first f' 0 ≫ F.map a)
    erw [← Category.assoc, homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv,
      ← F.map_comp]
    unfold CofiberSequence.first
    erw [← Category.assoc, homotopyCofiber.inlX_fstX, Category.id_comp,
      ← Category.assoc, homotopyCofiber.inlX_fstX, Category.id_comp]
  · change homotopyCofiber.inrX f' 1 ≫
      ((homotopyCofiber.mapHomologicalComplexObjXIso f F 1).inv ≫
        F.map (CofiberSequence.first f 0 ≫ a)) =
      homotopyCofiber.inrX f' 1 ≫ (CofiberSequence.first f' 0 ≫ F.map a)
    erw [← Category.assoc, homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv,
      ← F.map_comp]
    unfold CofiberSequence.first
    erw [← Category.assoc, homotopyCofiber.inrX_fstX, zero_comp, F.map_zero,
      ← Category.assoc, homotopyCofiber.inrX_fstX, zero_comp]

variable {A' B' : ChainComplex (Rep.{0} ℚ G) ℕ} (g : A' ⟶ B')
  (α : Arrow.mk f ⟶ Arrow.mk g) (b : A'.X 0 ⟶ W)

/-- A literal arrow comparison retains the corner map induced by its source arrow. -/
theorem coneArrow_cornerCochain :
    (homotopyCofiber.mapArrowHom f g (fun n => ⟨n+1,Cone.downRel n⟩) α).f 1 ≫
      coneCornerCochain g W b = coneCornerCochain f W (α.left.f 0 ≫ b) := by
  apply homotopyCofiber.ext_from_X f 0 1 (Cone.downRel 0)
  · rw [← Category.assoc, Cofiber.inl_map_arrow]
    unfold coneCornerCochain CofiberSequence.first
    rw [Category.assoc, ← Category.assoc (homotopyCofiber.inlX g 0 1 _),
      homotopyCofiber.inlX_fstX, Category.id_comp,
      ← Category.assoc, homotopyCofiber.inlX_fstX, Category.id_comp]
  · rw [← Category.assoc]
    unfold homotopyCofiber.mapArrowHom
    rw [homotopyCofiber.inrX_desc_f]
    change (α.right.f 1 ≫ homotopyCofiber.inrX g 1) ≫ coneCornerCochain g W b = _
    unfold coneCornerCochain CofiberSequence.first
    rw [Category.assoc, ← Category.assoc (homotopyCofiber.inrX g 1),
      homotopyCofiber.inrX_fstX, zero_comp, comp_zero,
      ← Category.assoc, homotopyCofiber.inrX_fstX, zero_comp]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
