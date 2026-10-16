module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeRestriction

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFullTransfer.Cofiber
open CategoryTheory Category Limits HomologicalComplex

theorem down (n : ℕ) : (ComplexShape.down ℕ).Rel (n+1) n := rfl

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  {A B K : ChainComplex C ℕ} (f : A ⟶ B) (v : B ⟶ K) (h : f ≫ v = 0)
  (F : C ⥤ D) [F.Additive]

/-- An additive functor transports a strict cone projection to the strict projected cone. -/
theorem map_desc :
    (homotopyCofiber.mapHomologicalComplexObjIso f F).inv ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (homotopyCofiber.desc f v (Homotopy.ofEq h)) =
    homotopyCofiber.desc ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f)
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map v)
      (Homotopy.ofEq (by rw [← Functor.map_comp,h,Functor.map_zero])) := by
  have hm : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map f ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map v = 0 := by
    rw [← Functor.map_comp,h,Functor.map_zero]
  apply HomologicalComplex.hom_ext
  intro n
  have hr (j : ℕ) :
      homotopyCofiber.inrX ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) j ≫
        ((homotopyCofiber.mapHomologicalComplexObjXIso f F j).inv ≫
          F.map ((homotopyCofiber.desc f v (Homotopy.ofEq h)).f j)) = F.map (v.f j) := by
    rw [← Category.assoc,homotopyCofiber.inrX_mapHomologicalComplexObjXIso_inv]
    exact (F.map_comp _ _).symm.trans (congrArg F.map (homotopyCofiber.inrX_desc_f f v (Homotopy.ofEq h) j))
  cases n with
  | zero =>
    apply homotopyCofiber.ext_from_X' ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) 0
      (by simp [ComplexShape.down_Rel])
    exact (hr 0).trans (homotopyCofiber.inrX_desc_f ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f)
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map v) (Homotopy.ofEq hm) 0).symm
  | succ n =>
    apply homotopyCofiber.ext_from_X ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) n (n+1) (down n)
    · have hl : homotopyCofiber.inlX ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) n (n+1) (down n) ≫
          ((homotopyCofiber.mapHomologicalComplexObjXIso f F (n+1)).inv ≫
            F.map ((homotopyCofiber.desc f v (Homotopy.ofEq h)).f (n+1))) = 0 := by
        rw [← Category.assoc,homotopyCofiber.inlX_mapHomologicalComplexObjXIso_inv]
        exact (F.map_comp _ _).symm.trans
          ((congrArg F.map (homotopyCofiber.inlX_desc_f f v (Homotopy.ofEq h) n (n+1) (down n))).trans
            (F.map_zero _ _))
      exact hl.trans (homotopyCofiber.inlX_desc_f ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f)
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map v) (Homotopy.ofEq hm) n (n+1) (down n)).symm
    · exact (hr (n+1)).trans (homotopyCofiber.inrX_desc_f ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f)
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map v) (Homotopy.ofEq hm) (n+1)).symm

section Arrow
variable {A' B' : ChainComplex C ℕ} (f' : A' ⟶ B')
    (α : Arrow.mk f ⟶ Arrow.mk f') (v' : B' ⟶ K) (h' : f' ≫ v' = 0)

theorem inl_map_arrow (n : ℕ) :
    homotopyCofiber.inlX f n (n+1) (down n) ≫
      (homotopyCofiber.mapArrowHom f f' (fun n => ⟨n+1,down n⟩) α).f (n+1) =
      α.left.f n ≫ homotopyCofiber.inlX f' n (n+1) (down n) := by
  unfold homotopyCofiber.mapArrowHom
  rw [homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans,Homotopy.ofEq,Homotopy.compLeft,zero_add,add_zero]
  rw [homotopyCofiber.inrCompHomotopy_hom f' (fun n => ⟨n+1,down n⟩) n (n+1) (down n)]

/-- Strict cone projections retain their specified middle map under an actual arrow comparison. -/
theorem map_arrow_desc :
    homotopyCofiber.mapArrowHom f f' (fun n => ⟨n+1,down n⟩) α ≫
      homotopyCofiber.desc f' v' (Homotopy.ofEq h') =
    homotopyCofiber.desc f (α.right ≫ v') (Homotopy.ofEq (by
      have hw : f ≫ α.right = α.left ≫ f' := α.w.symm
      rw [← Category.assoc,hw,Category.assoc,h',comp_zero])) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply homotopyCofiber.ext_from_X' f 0 (by simp [ComplexShape.down_Rel])
    change homotopyCofiber.inrX f 0 ≫
      ((homotopyCofiber.mapArrowHom f f' (fun n => ⟨n+1,down n⟩) α).f 0 ≫ _) = _
    rw [← Category.assoc]
    change (homotopyCofiber.inrX f 0 ≫ (homotopyCofiber.desc f _ _).f 0) ≫ _ = _
    rw [homotopyCofiber.inrX_desc_f]
    change (α.right.f 0 ≫ homotopyCofiber.inrX f' 0) ≫ _ = _
    rw [Category.assoc,homotopyCofiber.inrX_desc_f,homotopyCofiber.inrX_desc_f]
    rfl
  | succ n =>
    apply homotopyCofiber.ext_from_X f n (n+1) (down n)
    · change homotopyCofiber.inlX f n (n+1) (down n) ≫
        ((homotopyCofiber.mapArrowHom f f' (fun n => ⟨n+1,down n⟩) α).f (n+1) ≫ _) = _
      rw [← Category.assoc,inl_map_arrow,Category.assoc,homotopyCofiber.inlX_desc_f,
        homotopyCofiber.inlX_desc_f]
      exact comp_zero
    · change homotopyCofiber.inrX f (n+1) ≫
        ((homotopyCofiber.mapArrowHom f f' (fun n => ⟨n+1,down n⟩) α).f (n+1) ≫ _) = _
      rw [← Category.assoc]
      change (homotopyCofiber.inrX f (n+1) ≫ (homotopyCofiber.desc f _ _).f (n+1)) ≫ _ = _
      rw [homotopyCofiber.inrX_desc_f]
      change (α.right.f (n+1) ≫ homotopyCofiber.inrX f' (n+1)) ≫ _ = _
      rw [Category.assoc,homotopyCofiber.inrX_desc_f,homotopyCofiber.inrX_desc_f]
      rfl

end Arrow
end TernaryPoly.SymmetricSpaceBoundaryFullTransfer.Cofiber
