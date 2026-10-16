module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Gamma.NCanonical
public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.Core

@[expose] public section


/-!
# Injectivity of the face transport and the coboundary relation

`faceKerMap_injective`; from a vanishing sum of a holomorphic and an antiholomorphic seed class to a coboundary relation for the period cocycles.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormClassK
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

theorem H1map_injective {G : Type} [Group G] {V W : Rep ℂ G} (e : V ≅ W) :
    Function.Injective (groupCohomology.map (MonoidHom.id G) e.hom 1).hom := by
  have hm : CategoryTheory.Mono ((groupCohomology.functor ℂ G 1).map e.hom) := inferInstance
  rw [groupCohomology.functor_map] at hm
  exact (ModuleCat.mono_iff_injective _).1 hm

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

/-- The transport of radical-kernel classes to a plane cusp is injective. -/
theorem faceKerMap_injective : Function.Injective (faceKerMap N h n) := by
  intro x y hxy
  have h1 := faceEdge_kerMap N h n x
  have h2 := faceEdge_kerMap N h n y
  rw [hxy] at h1
  exact gammaNEdge_injective N n (H1map_injective (faceModIso N h n) (h1.symm.trans h2))


theorem seedBoundary_zero_face (f : TwTuple N n) (hf : seedBoundary N n f = 0) (i : PlaneFaces N) :
    gammaNSeedKerClass N n (f i false) + gammaNSeedConjKerClass N n (f i true) = 0 := by
  classical
  have h1 := seedBoundary_apply N n f i
  rw [hf] at h1
  apply faceKerMap_injective N n (planeFaceRepr i)
  rw [map_add, map_zero]
  apply Subtype.ext
  exact h1.symm

theorem hol_antihol_class_zero
    (F G : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ))
    (h0 : gammaNSeedKerClass N n F + gammaNSeedConjKerClass N n G = 0) :
    groupCohomology.H1π (binRep (CongruenceSubgroup.Gamma N) n) (holCocycle F) +
      groupCohomology.H1π (binRep (CongruenceSubgroup.Gamma N) n) (antiholCocycle G) = 0 := by
  have h1 := congrArg (gammaNEdge N n) h0
  rw [map_add, map_zero] at h1
  have e1 := gammaNSeedEdge (N := N) (n := n) F
  have e2 := gammaNSeedConjEdge (N := N) (n := n) G
  change gammaNEdge N n (gammaNSeedKerClass N n F) = _ at e1
  change gammaNEdge N n (gammaNSeedConjKerClass N n G) = _ at e2
  rw [e1, e2, ← smul_add] at h1
  have hne : (((n : ℂ) + 1)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  exact (smul_eq_zero.mp h1).resolve_left hne


theorem H1π_zero_iff {G : Type} [Group G] (A : Rep ℂ G) (c : groupCohomology.cocycles₁ A) :
    groupCohomology.H1π A c = 0 ↔ ∃ v : A, ∀ g, c.1 g = A.ρ g v - v := by
  rw [groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun g => ?_⟩
    have := congrFun hu g
    simp only [groupCohomology.d₀₁_hom_apply] at this
    exact this.symm
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    funext g
    simp only [groupCohomology.d₀₁_hom_apply]
    exact (hu g).symm

theorem hol_antihol_coboundary
    (F G : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ))
    (h0 : gammaNSeedKerClass N n F + gammaNSeedConjKerClass N n G = 0) :
    ∃ v : binRep (CongruenceSubgroup.Gamma N) n, ∀ m : CongruenceSubgroup.Gamma N,
      (holCocycle F).1 m + (antiholCocycle G).1 m = (binRep (CongruenceSubgroup.Gamma N) n).ρ m v - v := by
  have h1 := hol_antihol_class_zero N n F G h0
  rw [← map_add] at h1
  obtain ⟨v, hv⟩ := (H1π_zero_iff _ _).1 h1
  exact ⟨v, fun m => hv m⟩

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
