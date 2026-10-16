module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullInducedBarShapiro

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex Representation EquivariantSingularSmall groupCohomology

variable {G : Type} [Group G] (S : Subgroup G) (W : Rep.{0} ℚ G)

/-- The complete induced bar cochains identify with actual inhomogeneous subgroup cochains. -/
def inducedBarInhomogeneous : homCochains (inducedBarComplex S) W ≅
    inhomogeneousCochains (Rep.res S.subtype W) :=
  inducedBarShapiro S W ≪≫ (inhomogeneousCochainsIso (Rep.res S.subtype W)).symm

def inducedCoordinates0 : ((inducedBarComplex S).X 0 ⟶ W) ≃ₗ[ℚ] W :=
  ((HomologicalComplex.eval _ _ 0).mapIso (inducedBarInhomogeneous S W) ≪≫
    cochainsIso₀ (Rep.res S.subtype W)).toLinearEquiv

def inducedCoordinates1 : ((inducedBarComplex S).X 1 ⟶ W) ≃ₗ[ℚ] (S → W) :=
  ((HomologicalComplex.eval _ _ 1).mapIso (inducedBarInhomogeneous S W) ≪≫
    cochainsIso₁ (Rep.res S.subtype W)).toLinearEquiv

def inducedCoordinates2 : ((inducedBarComplex S).X 2 ⟶ W) ≃ₗ[ℚ] (S × S → W) :=
  ((HomologicalComplex.eval _ _ 2).mapIso (inducedBarInhomogeneous S W) ≪≫
    cochainsIso₂ (Rep.res S.subtype W)).toLinearEquiv

/-- Degree zero is evaluation at identity induction and the unique empty tuple. -/
theorem inducedCoordinates0_apply (c : (inducedBarComplex S).X 0 ⟶ W) :
    inducedCoordinates0 S W c = c.hom (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 0).ρ 1
      (Finsupp.single default (MonoidAlgebra.single 1 1))) := rfl

/-- Degree one retains literal subgroup elements and identity induction. -/
theorem inducedCoordinates1_apply (c : (inducedBarComplex S).X 1 ⟶ W) (g : S) :
    inducedCoordinates1 S W c g = c.hom (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 1).ρ 1
      (Finsupp.single (fun _ => g) (MonoidAlgebra.single 1 1))) := rfl

theorem inducedCoordinates2_apply (c : (inducedBarComplex S).X 2 ⟶ W) (g h : S) :
    inducedCoordinates2 S W c (g,h) = c.hom (IndV.mk S.subtype ((Rep.barResolution ℚ S).complex.X 2).ρ 1
      (Finsupp.single ![g,h] (MonoidAlgebra.single 1 1))) := rfl

/-- Exact low-degree differential compatibility, with the genuine subgroup action. -/
theorem inducedCoordinates_d0 (c : (inducedBarComplex S).X 0 ⟶ W) :
    inducedCoordinates1 S W ((inducedBarComplex S).d 1 0 ≫ c) =
    d₀₁ (Rep.res S.subtype W) (inducedCoordinates0 S W c) := by
  have h := congrArg (fun f => f c) ((inducedBarInhomogeneous S W).hom.comm 0 1)
  have h' := congrArg (fun f => f ((inducedBarInhomogeneous S W).hom.f 0 c))
    (comp_d₀₁_eq (Rep.res S.subtype W))
  exact (congrArg (fun x => (cochainsIso₁ (Rep.res S.subtype W)).hom x) h.symm).trans h'.symm

theorem inducedCoordinates_d1 (c : (inducedBarComplex S).X 1 ⟶ W) :
    inducedCoordinates2 S W ((inducedBarComplex S).d 2 1 ≫ c) =
    d₁₂ (Rep.res S.subtype W) (inducedCoordinates1 S W c) := by
  have h := congrArg (fun f => f c) ((inducedBarInhomogeneous S W).hom.comm 1 2)
  have h' := congrArg (fun f => f ((inducedBarInhomogeneous S W).hom.f 1 c))
    (comp_d₁₂_eq (Rep.res S.subtype W))
  exact (congrArg (fun x => (cochainsIso₂ (Rep.res S.subtype W)).hom x) h.symm).trans h'.symm

variable (T : Subgroup G) (hST : S ≤ T)

theorem inducedCoordinates_restrict0 (c : (inducedBarComplex T).X 0 ⟶ W) :
    inducedCoordinates0 S W ((inducedBarMap S T hST).f 0 ≫ c) = inducedCoordinates0 T W c := by
  rw [inducedCoordinates0_apply,inducedCoordinates0_apply]
  change c.hom ((inducedBarDegree S T hST 0).hom (IndV.mk _ _ 1 _)) = _
  refine (congrArg (fun x => c.hom x) (inducedBarDegree_mk S T hST 0 1
    (Finsupp.single default (MonoidAlgebra.single 1 1)))).trans ?_
  have h := SingularCoverRestriction.barDegreeMap_generator (Subgroup.inclusion hST) 0 default
  have he : (Subgroup.inclusion hST) ∘ (default : Fin 0 → S) = (default : Fin 0 → T) :=
    Subsingleton.elim _ _
  rw [he] at h
  exact congrArg (fun x => c.hom (IndV.mk _ _ 1 x)) h

theorem inducedCoordinates_restrict1 (c : (inducedBarComplex T).X 1 ⟶ W) (g : S) :
    inducedCoordinates1 S W ((inducedBarMap S T hST).f 1 ≫ c) g =
      inducedCoordinates1 T W c (Subgroup.inclusion hST g) := by
  rw [inducedCoordinates1_apply,inducedCoordinates1_apply]
  change c.hom ((inducedBarDegree S T hST 1).hom (IndV.mk _ _ 1 _)) = _
  refine (congrArg (fun x => c.hom x) (inducedBarDegree_mk S T hST 1 1
    (Finsupp.single (fun _ => g) (MonoidAlgebra.single 1 1)))).trans ?_
  exact congrArg (fun x => c.hom (IndV.mk _ _ 1 x))
    (SingularCoverRestriction.barDegreeMap_generator (Subgroup.inclusion hST) 1 (fun _ => g))

end TernaryPoly.SymmetricSpaceBoundaryFull
