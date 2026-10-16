module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ModuleClasses

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits

variable {R : Type*} [Ring R] {S T : ShortComplex (ModuleCat.{0} R)}

/-- A genuine short-complex map is a quasi-isomorphism when every target cocycle lifts
modulo an actual boundary and every source cocycle whose image is a boundary is itself a boundary. -/
theorem module_quasiIso_of_cycle_boundary_lifts (f : S ⟶ T)
    (hs : ∀ x : T.X₂, T.g.hom x = 0 →
      ∃ z : S.X₂, ∃ _hz : S.g.hom z = 0, ∃ y : T.X₁, x = T.f.hom y + f.τ₂.hom z)
    (hi : ∀ z : S.X₂, S.g.hom z = 0 → ∀ y : T.X₁,
      f.τ₂.hom z = T.f.hom y → ∃ t : S.X₁, S.f.hom t = z) :
    ShortComplex.QuasiIso f := by
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (injective_iff_map_eq_zero (ShortComplex.homologyMap f).hom).mpr
    intro c hc
    obtain ⟨z,hz,rfl⟩ := moduleClass_surjective S c
    rw [moduleClass_natural] at hc
    obtain ⟨y,hy⟩ := (moduleClass_eq_zero_iff T _ _).mp hc
    exact (moduleClass_eq_zero_iff S z hz).mpr (hi z hz y hy.symm)
  · intro c
    obtain ⟨x,hx,rfl⟩ := moduleClass_surjective T c
    obtain ⟨z,hz,y,hy⟩ := hs x hx
    refine ⟨moduleClass S z hz, ?_⟩
    rw [moduleClass_natural, moduleClass_eq_iff]
    refine ⟨-y, ?_⟩
    rw [map_neg, hy]
    abel

end TernaryPoly.SmoothSingularGlobal
