module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Subobject.Comma
public import Mathlib.Topology.Sheaves.PUnit

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- Restriction to the same quotient open is literally the identity on equivariant forms. -/
theorem restrictEquivariant_id (U : Set OrbitSpace) (n : ℕ) :
    restrictEquivariant ρ (Subset.refl U) n = LinearMap.id := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact restrictEquivariant_apply ρ _ w hx

/-- Nested actual quotient restrictions compose without changing a representative. -/
theorem restrictEquivariant_comp {U V W : Set OrbitSpace} (hVU : V ⊆ U) (hWV : W ⊆ V) (n : ℕ) :
    (restrictEquivariant ρ hWV n).comp (restrictEquivariant ρ hVU n) =
      restrictEquivariant ρ (hWV.trans hVU) n := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change ((restrictEquivariant ρ hWV n (restrictEquivariant ρ hVU n w)).val : RawForm _ F n) x = _
  rw [restrictEquivariant_apply ρ _ _ hx,
    restrictEquivariant_apply ρ _ w (liftedDomain_mono hWV hx), restrictEquivariant_apply ρ _ w hx]

/-- The genuine degree-n smooth equivariant-form presheaf on the arithmetic quotient. -/
def formPresheaf (n : ℕ) : TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace) where
  obj U := ModuleCat.of ℝ (EquivariantForm ρ (U.unop : Set OrbitSpace) n)
  map f := ModuleCat.ofHom (restrictEquivariant ρ f.unop.le n)
  map_id U := by
    apply ModuleCat.hom_ext
    exact restrictEquivariant_id ρ _ n
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (restrictEquivariant_comp ρ f.unop.le g.unop.le n).symm

/-- The literal exterior derivative is a natural transformation of the actual form presheaves. -/
def formDifferential (n : ℕ) : formPresheaf ρ n ⟶ formPresheaf ρ (n+1) where
  app U := ModuleCat.ofHom (differential ρ U.unop.isOpen n)
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact (restrictEquivariant_d ρ U.unop.isOpen V.unop.isOpen f.unop.le w).symm

/-- Exterior differentiation squares to zero as an actual presheaf morphism. -/
theorem formDifferential_squared (n : ℕ) : formDifferential ρ n ≫ formDifferential ρ (n+1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact differential_squared ρ U.unop.isOpen n w

/-- The actual smooth de Rham presheaf complex on the quotient. -/
def formPresheafComplex : CochainComplex (TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace)) ℕ :=
  CochainComplex.of (formPresheaf ρ) (formDifferential ρ) (formDifferential_squared ρ)

end TernaryPoly.SmoothSingularGlobal
