module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularNaturality
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormAugmentation
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SymmetricSpaceCovering

/-- Genuine left-exact sheafification of real module presheaves on the quotient. -/
def quotientSheafification : TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace) ⥤
    (TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ) :=
  presheafToSheaf (Opens.grothendieckTopology (TopCat.of OrbitSpace)) (ModuleCat ℝ)

/-- The actual sheafification functor preserves zero maps. -/
instance quotientSheafification_preservesZeroMorphisms :
    quotientSheafification.PreservesZeroMorphisms :=
  inferInstanceAs ((presheafToSheaf (Opens.grothendieckTopology (TopCat.of OrbitSpace))
    (ModuleCat ℝ)).PreservesZeroMorphisms)

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Sheafification of the genuine real equivariant singular presheaf in degree n. -/
def singularSheaf (n : ℕ) : (TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ) :=
  quotientSheafification.obj (singularPresheaf ρ n)

/-- The differential on the actual sheafified singular model is the image of the literal coboundary. -/
def singularSheafDifferential (n : ℕ) : singularSheaf ρ n ⟶ singularSheaf ρ (n+1) :=
  quotientSheafification.map (singularPresheafDifferential ρ n)

/-- The genuine sheafified singular differential squares to zero. -/
theorem singularSheafDifferential_squared (n : ℕ) :
    singularSheafDifferential ρ n ≫ singularSheafDifferential ρ (n+1) = 0 := by
  change quotientSheafification.map _ ≫ quotientSheafification.map _ = _
  rw [← quotientSheafification.map_comp, singularPresheafDifferential_squared,
    Functor.map_zero]
  rfl

/-- The actual sheafified real equivariant singular complex. -/
def singularSheafComplex : CochainComplex ((TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ)) ℕ :=
  CochainComplex.of (singularSheaf ρ) (singularSheafDifferential ρ)
    (singularSheafDifferential_squared ρ)

/-- The actual coefficient sheaf is unchanged by genuine sheafification. -/
def coefficientSheafificationIso : coefficientSheaf ρ ≅
    quotientSheafification.obj (coefficientPresheaf ρ) :=
  sheafificationIso (coefficientSheaf ρ)

/-- The actual coefficient-to-singular sheaf map is induced by the literal presheaf augmentation. -/
def coefficientToSingularSheaf : coefficientSheaf ρ ⟶ singularSheaf ρ 0 :=
  (coefficientSheafificationIso ρ).hom ≫ quotientSheafification.map (coefficientToSingular ρ)

/-- The true coefficient augmentation has zero differential in the sheafified singular complex. -/
theorem coefficientToSingularSheaf_closed :
    coefficientToSingularSheaf ρ ≫ singularSheafDifferential ρ 0 = 0 := by
  change ((coefficientSheafificationIso ρ).hom ≫ quotientSheafification.map _) ≫
    quotientSheafification.map _ = _
  rw [Category.assoc, ← quotientSheafification.map_comp, coefficientToSingular_closed,
    Functor.map_zero, Limits.comp_zero]
  rfl

/-- The actual locally constant coefficient augmentation of the actual singular sheaf complex. -/
def singularSheafAugmentation :
    (CochainComplex.single₀ ((TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ))).obj (coefficientSheaf ρ) ⟶
      singularSheafComplex ρ :=
  (CochainComplex.fromSingle₀Equiv (singularSheafComplex ρ) (coefficientSheaf ρ)).symm
    ⟨coefficientToSingularSheaf ρ, coefficientToSingularSheaf_closed ρ⟩

/-- The singular sheaf augmentation retains the actual degree-zero map. -/
theorem singularSheafAugmentation_f_zero :
    (singularSheafAugmentation ρ).f 0 = coefficientToSingularSheaf ρ :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end TernaryPoly.SmoothSingularGlobal
