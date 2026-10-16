module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Setup
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.QSideNatural
public import TernaryPeriodPolynomials.GroupCohomology.Homology.BarMaps

@[expose] public section


/-!
# The Hochschild-Serre set-up for an arbitrary projective resolution

Formalized by Claude Sonnet 5.5.

For a projective resolution `R` of the trivial `P`-module, `YAR R A = A ⊗ R` and `ZR U R A` its complex of
`U`-coinvariants with the `P/U`-action, as `ZP U A` is for the bar resolution.
-/

open CategoryTheory MonoidalCategory Representation Limits
open scoped Classical
open TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal]
  (R : ProjectiveResolution (Rep.trivial ℚ P ℚ)) (A : Rep.{0} ℚ P)

/-- `A ⊗ R`. -/
abbrev YAR : ChainComplex (Rep.{0} ℚ P) ℕ :=
  ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj R.complex

/-- The complex of `U`-coinvariants of `A ⊗ R`, with its `P/U`-action. -/
abbrev ZR : ChainComplex (Rep.{0} ℚ (P ⧸ U)) ℕ :=
  ((Phi U).mapHomologicalComplex (ComplexShape.down ℕ)).obj (YAR R A)

theorem ZR_projective (j : ℕ) : Projective ((ZR U R A).X j) := by
  have h1 : Projective ((YAR R A).X j) :=
    (tensorLeft A).projective_obj_of_projective (R.projective j)
  exact Phi_projective U _

/-- The complex `(Z ⊗ 1)_{P/U}` is the complex of `P`-coinvariants of `A ⊗ R`. -/
def ZIsoR : CxF (ZR U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U))) ≅ CxK (YAR R A) :=
  HomologicalComplex.Hom.isoOfComponents (fun j => (coinvIso U).app ((YAR R A).X j))
    (fun i j _ => ((coinvIso U).hom.naturality ((YAR R A).d i j)).symm)

/-- `H_n(P, A) ≅ H_n((Z ⊗ 1)_{P/U})`, through `R`. -/
def groupHomologyZIsoR (n : ℕ) :
    groupHomology A n ≅ (CxF (ZR U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))).homology n :=
  groupHomologyIso A n R ≪≫ (HomologicalComplex.homologyMapIso (ZIsoR U R A) n).symm

/-- The comparison `bar(P) → R` over the identity of the trivial module. -/
def fR : (Rep.barResolution ℚ P).complex ⟶ R.complex :=
  ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ P ℚ)) (Rep.barResolution ℚ P) R

theorem fR_comm : fR R ≫ R.π = (Rep.barResolution ℚ P).π ≫ (ChainComplex.single₀ _).map (𝟙 _) :=
  ProjectiveResolution.lift_commutes _ _ _

/-- `A ⊗ f`. -/
def fY : YA A ⟶ YAR R A := ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map (fR R)

/-- The induced chain map of `P/U`-complexes `ZP U A ⟶ ZR U R A`. -/
def fZ : ZP U A ⟶ ZR U R A := ((Phi U).mapHomologicalComplex (ComplexShape.down ℕ)).map (fY R A)

theorem fZ_f (j : ℕ) : (fZ U R A).f j = (Phi U).map ((fY R A).f j) := rfl

theorem fZ_square : CxMapZ (fZ U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U))) ≫ (ZIsoR U R A).hom =
    (ZIso U A).hom ≫ ((cK (k := ℚ) (K := P)).mapHomologicalComplex (ComplexShape.down ℕ)).map (fY R A) := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  simp only [HomologicalComplex.comp_f, CxMapZ_f]
  exact ((coinvIso U).hom.naturality ((fY R A).f j))

theorem groupHomologyZIso_compat (n : ℕ) :
    (groupHomologyZIso U A n).hom ≫
        HomologicalComplex.homologyMap (CxMapZ (fZ U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))) n =
      (groupHomologyZIsoR U R A n).hom := by
  have comm : (fR R).f 0 ≫ R.π.f 0 = (Rep.barResolution ℚ P).π.f 0 := by
    have h := congrArg (fun t => t.f 0) (fR_comm R)
    simp only [HomologicalComplex.comp_f] at h
    rw [(ChainComplex.single₀ _).map_id, HomologicalComplex.id_f, Category.comp_id] at h
    exact h
  have h1 := groupHomologyIso_hom_comp (k := ℚ) (G := P) A n (P := Rep.barResolution ℚ P) (Q := R) (fR R) comm
  have h2 : CxMapZ (fZ U R A) (𝟙_ (Rep.{0} ℚ (P ⧸ U))) =
      (ZIso U A).hom ≫ ((cK (k := ℚ) (K := P)).mapHomologicalComplex (ComplexShape.down ℕ)).map (fY R A) ≫
        (ZIsoR U R A).inv := by
    rw [← Category.assoc, ← fZ_square, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h3 : (groupHomologyZIso U A n).hom = (eK A n).hom ≫ (HomologicalComplex.homologyMapIso (ZIso U A) n).inv := rfl
  have h4 : (groupHomologyZIsoR U R A n).hom =
      (groupHomologyIso A n R).hom ≫ (HomologicalComplex.homologyMapIso (ZIsoR U R A) n).inv := rfl
  rw [h3, h4, ← h1, h2, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  have h5 : (HomologicalComplex.homologyMapIso (ZIso U A) n).inv ≫
      HomologicalComplex.homologyMap (ZIso U A).hom n = 𝟙 _ := Iso.inv_hom_id _
  rw [reassoc_of% h5]
  rfl

/-- `fZ` is a homotopy equivalence of complexes of `P/U`-representations. -/
def fZHomotopyEquiv : HomotopyEquiv (ZP U A) (ZR U R A) :=
  (Phi U).mapHomotopyEquiv ((tensorLeft A).mapHomotopyEquiv
    (ProjectiveResolution.homotopyEquiv (Rep.barResolution ℚ P) R))

theorem fZHomotopyEquiv_hom : (fZHomotopyEquiv U R A).hom = fZ U R A := rfl

instance fZ_homology_iso (n : ℕ) : IsIso (HomologicalComplex.homologyMap (fZ U R A) n) :=
  inferInstanceAs (IsIso ((fZHomotopyEquiv U R A).toHomologyIso n).hom)

theorem isZero_ZR_homology (n : ℕ) (h : IsZero ((ZP U A).homology n)) : IsZero ((ZR U R A).homology n) :=
  IsZero.of_iso h (asIso (HomologicalComplex.homologyMap (fZ U R A) n)).symm

theorem isZero_ZR_homology_of_group (n : ℕ) (h : IsZero (groupHomology (Rep.res U.subtype A) n)) :
    IsZero ((ZR U R A).homology n) :=
  isZero_ZR_homology U R A n (isZero_ZP_homology U A n h)

end TernaryPeriodPolynomials.Argument.HochschildSerre
