module

public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularBoundaryRestriction
open CategoryTheory

variable {α β : Type*} {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- Linear extension by zero from the image of a map, using its unique preimage when injective. -/
def zeroExtension (f : α → β) : (α → M) →ₗ[ℚ] (β → M) := by
  classical
  exact {
    toFun := fun c y => if h : ∃ x,f x=y then c h.choose else 0
    map_add' := by intro c d; funext y; by_cases h : ∃ x,f x=y <;> simp [h]
    map_smul' := by intro r c; funext y; by_cases h : ∃ x,f x=y <;> simp [h] }

/-- On an injective image, the extension evaluates to the original coefficient. -/
theorem zeroExtension_image (f : α → β) (hf : Function.Injective f) (c : α → M) (x : α) :
    zeroExtension f c (f x)=c x := by
  classical
  have h : ∃ y,f y=f x := ⟨x,rfl⟩
  simp only [zeroExtension,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_left h]
  exact congrArg c (hf h.choose_spec)

theorem zeroExtension_outside (f : α → β) (c : α → M) (y : β)
    (hy : y∉Set.range f) : zeroExtension f c y=0 := by
  classical
  change ¬∃ x,f x=y at hy
  simp only [zeroExtension,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_right hy]

variable {G : Type} [Group G] [MulAction G α] [MulAction G β]

/-- The complement of the image of an equivariant map is invariant. -/
theorem outside_image_smul (f : α → β) (hf : ∀ (g : G) x,f (g • x)=g • f x)
    (g : G) (y : β) (hy : y∉Set.range f) : g • y∉Set.range f := by
  rintro ⟨x,hx⟩
  apply hy
  refine ⟨g⁻¹ • x,?_⟩
  rw [hf,hx,inv_smul_smul]

/-- Extension by zero is equivariant because the injective image and its complement are invariant. -/
theorem zeroExtension_equivariant (f : α → β) (hf : Function.Injective f)
    (he : ∀ (g : G) x,f (g • x)=g • f x) (V : Rep ℚ G) (c : α → V)
    (hc : ∀ (g : G) x,c (g • x)=V.ρ g (c x)) (g : G) (y : β) :
    zeroExtension f c (g • y)=V.ρ g (zeroExtension f c y) := by
  by_cases hy : y∈Set.range f
  · obtain ⟨x,rfl⟩ := hy
    rw [←he,zeroExtension_image f hf,zeroExtension_image f hf,hc]
  · rw [zeroExtension_outside f c y hy,
      zeroExtension_outside f c (g • y) (outside_image_smul f he g y hy),map_zero]

end TernaryPoly.SingularBoundaryRestriction
