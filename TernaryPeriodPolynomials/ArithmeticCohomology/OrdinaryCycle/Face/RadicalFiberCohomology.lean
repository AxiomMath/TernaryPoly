module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.FirstCohomologyCocycles

@[expose] public section


open CategoryTheory
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open groupCohomology

variable {G I V : Type} [Group G] [AddCommGroup V] [Module ℚ V]
variable (ρ : Representation ℚ G (I → V)) (σ : Representation ℚ G V)
variable (hρ : ∀ (g : G) (v : I → V) (r : I),ρ g v r=σ g (v r))

/-- Actual fiber evaluation is an equivariant coefficient morphism when the group fixes the fibers. -/
def fiberCoefficientHom (r : I) :
    Rep.res (MonoidHom.id G) (Rep.of ρ) ⟶ Rep.of σ :=
  Rep.ofHom ⟨LinearMap.proj r,by
    intro g
    apply LinearMap.ext
    intro v
    exact hρ g v r⟩

/-- The actual induced degree-one cohomology map of a fiber evaluation. -/
def fiberH1Map (r : I) : groupCohomology (Rep.of ρ) 1 ⟶ groupCohomology (Rep.of σ) 1 :=
  groupCohomology.map (MonoidHom.id G) (fiberCoefficientHom ρ σ hρ r) 1

/-- A genuine function-valued H¹ class is zero when every actual fiber class is zero. -/
theorem fiberH1_jointly_injective (x : groupCohomology (Rep.of ρ) 1)
    (hx : ∀ r,fiberH1Map ρ σ hρ r x=0) : x=0 := by
  revert hx
  refine H1_induction_on x ?_
  intro c hc
  have hv : ∀ r,∃ v : V,∀ g,σ g v-v=c g r := by
    intro r
    have h := hc r
    change groupCohomology.map (MonoidHom.id G) (fiberCoefficientHom ρ σ hρ r) 1
      (H1π (Rep.of ρ) c)=0 at h
    rw [H1π_comp_map_apply,H1π_eq_zero_iff] at h
    obtain ⟨v,hv⟩ := h
    refine ⟨v,fun g => ?_⟩
    exact congrFun hv g
  choose v hv using hv
  rw [H1π_eq_zero_iff]
  refine ⟨v,?_⟩
  funext g r
  change ρ g v r-v r=c g r
  rw [hρ]
  exact hv r g

/-- Fiber evaluation intertwines actual normalizer cohomology maps whenever it intertwines
both displayed coefficient morphisms. -/
theorem fiberH1Map_natural (f : G →* G)
    (φ : Rep.res f (Rep.of ρ) ⟶ Rep.of ρ)
    (ψ : Rep.res f (Rep.of σ) ⟶ Rep.of σ)
    (r : I) (hφ : ∀ v : I → V,φ v r=ψ (v r))
    (x : groupCohomology (Rep.of ρ) 1) :
    fiberH1Map ρ σ hρ r (groupCohomology.map f φ 1 x)=
      groupCohomology.map f ψ 1 (fiberH1Map ρ σ hρ r x) := by
  refine H1_induction_on x ?_
  intro c
  simp only [fiberH1Map,H1π_comp_map_apply]
  apply congrArg (H1π (Rep.of σ))
  apply cocycles₁_ext
  intro g
  exact hφ (c (f g))

end TernaryPoly.OrdinaryFaceRadical
