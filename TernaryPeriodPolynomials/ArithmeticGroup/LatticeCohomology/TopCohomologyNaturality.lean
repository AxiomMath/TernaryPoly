module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyBarComparison
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyAlternating

@[expose] public section


open CategoryTheory CategoryTheory.Limits

noncomputable section
namespace TernaryPoly.LatticeTopCohomology

variable (A : Rep ℚ Lattice)

/-- The cohomology quotient isomorphism defined by the explicit oriented grid-to-bar comparison. -/
def explicitQuotientIso : groupCohomology A 2 ≅ ModuleCat.of ℚ (A ⧸ relations A) :=
  (cochainsComparison A).toHomologyIso 2 ≪≫ homologyQuotientIso A

@[reassoc] theorem cokernelIso_π {U V : ModuleCat ℚ} (f : U ⟶ V) :
    cokernel.π f ≫ (ModuleCat.cokernelIsoRangeQuotient f).hom =
      ModuleCat.ofHom (LinearMap.range f.hom).mkQ :=
  ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom f

@[reassoc] theorem shortTopQuotient_π (S : ShortComplex (ModuleCat ℚ)) (hg : S.g = 0) :
    S.homologyπ ≫ (ShortComplex.LeftHomologyData.ofHasCokernel S hg).homologyIso.hom ≫
      (ModuleCat.cokernelIsoRangeQuotient S.f).hom =
      S.iCycles ≫ ModuleCat.ofHom (LinearMap.range S.f.hom).mkQ := by
  let D := ShortComplex.LeftHomologyData.ofHasCokernel S hg
  have hi : D.cyclesIso.hom = S.iCycles := by
    have h := D.cyclesIso_hom_comp_i
    change D.cyclesIso.hom ≫ 𝟙 S.X₂ = S.iCycles at h
    exact (Category.comp_id D.cyclesIso.hom).symm.trans h
  erw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  change D.cyclesIso.hom ≫ cokernel.π S.f ≫ (ModuleCat.cokernelIsoRangeQuotient S.f).hom = _
  erw [hi, cokernelIso_π]
  rfl

@[reassoc] theorem homologyQuotientIso_π :
    (homComplex A).homologyπ 2 ≫ (homologyQuotientIso A).hom =
      (homComplex A).iCycles 2 ≫ (topCoordinate A).toModuleIso.hom ≫
        ModuleCat.ofHom (quotientMap A) := by
  dsimp only [homologyQuotientIso]
  dsimp only [Iso.trans_hom]
  erw [HomologicalComplex.π_homologyIsoSc'_hom_assoc]
  erw [← Category.assoc _ (ModuleCat.cokernelIsoRangeQuotient ((homComplex A).d 1 2)).hom,
    shortTopQuotient_π_assoc]
  erw [← Category.assoc, HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  congr 1

@[reassoc] theorem explicitQuotientIso_π :
    groupCohomology.π A 2 ≫ (explicitQuotientIso A).hom =
      groupCohomology.iCocycles A 2 ≫ (cochainsComparison A).hom.f 2 ≫
        (topCoordinate A).toModuleIso.hom ≫ ModuleCat.ofHom (quotientMap A) := by
  change (groupCohomology.inhomogeneousCochains A).homologyπ 2 ≫
    HomologicalComplex.homologyMap (cochainsComparison A).hom 2 ≫
    (homologyQuotientIso A).hom =
    (groupCohomology.inhomogeneousCochains A).iCycles 2 ≫ (cochainsComparison A).hom.f 2 ≫
      (topCoordinate A).toModuleIso.hom ≫ ModuleCat.ofHom (quotientMap A)
  rw [HomologicalComplex.homologyπ_naturality_assoc, homologyQuotientIso_π]
  simp only [← Category.assoc, HomologicalComplex.cyclesMap_i]

/-- On a genuine two-cocycle, the class coordinate is its antisymmetric basis value. -/
theorem explicitQuotientIso_H2π (c : groupCohomology.cocycles₂ A) :
    (explicitQuotientIso A).hom (groupCohomology.H2π A c) =
      alternatingValue A c first second := by
  have h := congrArg (fun f => f c) (congrArg
    (fun f => (groupCohomology.isoCocycles₂ A).inv ≫ f) (explicitQuotientIso_π A))
  simp only [← Category.assoc, groupCohomology.isoCocycles₂_inv_comp_iCocycles] at h
  change (explicitQuotientIso A).hom (groupCohomology.H2π A c) = _ at h
  rw [h]
  change quotientMap A (topCoordinate A ((cochainsComparison A).hom.f 2
    (fun g => c (g 0,g 1)))) = _
  rw [cochainsComparison_two]
  rfl

variable {A} {B : Rep ℚ Lattice} (e : Lattice ≃* Lattice) (f : Rep.res e.toMonoidHom A ⟶ B)

theorem quotientCoefficient_ρ (g : Lattice) (v : A) :
    quotientMap B (f.hom (A.ρ g v)) = quotientMap B (f.hom v) := by
  have h := Rep.hom_comm_apply f (e.symm g) v
  change f.hom (A.ρ (e (e.symm g)) v) = B.ρ (e.symm g) (f.hom v) at h
  rw [e.apply_symm_apply] at h
  rw [h, quotientMap_ρ]

theorem quotientCoefficient_relations :
    relations A ≤ LinearMap.ker ((quotientMap B).comp f.hom.toLinearMap) := by
  apply sup_le
  all_goals
    rintro v ⟨w, rfl⟩
    change quotientMap B (f.hom (A.ρ _ w - w)) = 0
    rw [map_sub, map_sub, quotientCoefficient_ρ e f, sub_self]

/-- The genuine semilinear coefficient morphism descends to coinvariants. -/
def quotientCoefficientMap : (A ⧸ relations A) →ₗ[ℚ] (B ⧸ relations B) :=
  (relations A).liftQ ((quotientMap B).comp f.hom.toLinearMap) (quotientCoefficient_relations e f)

@[simp] theorem quotientCoefficientMap_mk (v : A) :
    quotientCoefficientMap e f (quotientMap A v) = quotientMap B (f.hom v) := rfl

theorem alternatingValue_map (c : groupCohomology.cocycles₂ A) (g h : Lattice) :
    alternatingValue B (groupCohomology.mapCocycles₂ e.toMonoidHom f c) g h =
      quotientCoefficientMap e f (alternatingValue A c (e g) (e h)) := by
  change quotientMap B (f.hom (c (e g,e h)) - f.hom (c (e h,e g))) =
    quotientMap B (f.hom (c (e g,e h) - c (e h,e g)))
  exact congrArg (quotientMap B) (map_sub f.hom _ _).symm

/-- The determinant of a lattice automorphism in the chosen oriented basis. -/
def latticeDeterminant (e : Lattice ≃* Lattice) : ℤ :=
  (e first).toAdd.1 * (e second).toAdd.2 - (e first).toAdd.2 * (e second).toAdd.1

/-- Full actual group-change naturality, including the determinant factor. -/
theorem explicitQuotientIso_natural (v : groupCohomology A 2) :
    (explicitQuotientIso B).hom (groupCohomology.map e.toMonoidHom f 2 v) =
      latticeDeterminant e • quotientCoefficientMap e f ((explicitQuotientIso A).hom v) := by
  induction v using groupCohomology.H2_induction_on with
  | h c =>
    rw [groupCohomology.H2π_comp_map_apply]
    rw [explicitQuotientIso_H2π, alternatingValue_map,
      alternatingValue_determinant, map_zsmul, explicitQuotientIso_H2π]
    rfl

end TernaryPoly.LatticeTopCohomology
