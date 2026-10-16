module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoverAction
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormSheaf
public import Mathlib.Topology.LocallyConstant.Algebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SmoothCoveringDeRham SymmetricSpaceCovering
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The coefficient sections are actual locally constant equivariant functions on the cover. -/
def coefficientSections (U : Set OrbitSpace) : Submodule ℝ (LocallyConstant (CoverOpen U) F) where
  carrier := {f | ∀ (g : DeckGroup) (x : CoverOpen U), f (g • x) = ρ g (f x)}
  zero_mem' := by intro g x; exact (map_zero (ρ g)).symm
  add_mem' := by
    intro f k hf hk g x
    change f (g • x) + k (g • x) = ρ g (f x + k x)
    rw [hf, hk, map_add]
  smul_mem' := by
    intro a f hf g x
    change a • f (g • x) = ρ g (a • f x)
    rw [hf, map_smul]

/-- Actual coefficient restriction is precomposition by lifted-domain inclusion. -/
def coefficientRestriction {U V : Set OrbitSpace} (hVU : V ⊆ U) :
    coefficientSections ρ U →ₗ[ℝ] coefficientSections ρ V where
  toFun f := ⟨LocallyConstant.comap (coverInclusion hVU).hom f.val, by
    intro g x
    exact f.property g (coverInclusion hVU x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coefficient restrictions evaluate on the literal same lifted coordinate. -/
theorem coefficientRestriction_apply {U V : Set OrbitSpace} (hVU : V ⊆ U)
    (f : coefficientSections ρ U) (x : CoverOpen V) :
    (coefficientRestriction ρ hVU f).val x = f.val (coverInclusion hVU x) := rfl

/-- Restriction to the same quotient subset is the identity on actual coefficient functions. -/
theorem coefficientRestriction_id (U : Set OrbitSpace) :
    coefficientRestriction ρ (Subset.refl U) = LinearMap.id := rfl

/-- Actual locally constant coefficient restrictions compose. -/
theorem coefficientRestriction_comp {U V W : Set OrbitSpace} (hVU : V ⊆ U) (hWV : W ⊆ V) :
    (coefficientRestriction ρ hWV).comp (coefficientRestriction ρ hVU) =
      coefficientRestriction ρ (hWV.trans hVU) := rfl

/-- The real local-coefficient presheaf in the convention f(gx)=ρ(g)f(x). -/
def coefficientPresheaf : TopCat.Presheaf (ModuleCat ℝ) (TopCat.of OrbitSpace) where
  obj U := ModuleCat.of ℝ (coefficientSections ρ (U.unop : Set OrbitSpace))
  map f := ModuleCat.ofHom (coefficientRestriction ρ f.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

end TernaryPoly.SmoothSingularGlobal
