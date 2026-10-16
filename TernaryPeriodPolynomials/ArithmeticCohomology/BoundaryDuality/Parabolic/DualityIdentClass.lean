module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelThree

@[expose] public section


/-!
# Parabolic cocycles from parabolic classes

A crossed homomorphism whose class is parabolic is itself parabolic: the parabolic condition (the
restriction to `N` has a primitive triple at `a`, `g₂`, `(a g₂)⁻¹`) is stable under adding a
coboundary, because the boundary of a vector `w` has the primitive triple `(w, w, w)`.  Hence the
membership of a cocycle in the parabolic cocycles can be read on its class.  Applied to the
cocycles `±` an edge class, this gives the parabolicity of the cocycle of any bridge whose class is
a multiple of a parabolic edge class.

* `mem_parabolicSub_of_mem_parabolicClasses`: the generic statement for a cohomology model.
* `LevelOne.mem_parabolicCocycles_of_projectH1_mem` and
  `LevelThree.mem_parabolicCrossed_of_mem`: the two models of `ParabolicDuality`.
* `LevelOne.mem_parabolicCocycles_of_eq_neg`, `LevelOne.projectH1_ne_zero_of_eq_neg`: the two
  consequences used for a cocycle whose class is the negative of a given class.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality

open TripleModel LinearDuality CocycleBridge EpsilonSplit

section Generic

variable {Γ N V K H : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup K]
  [Module ℂ K] [AddCommGroup H] [Module ℂ H]

/-- **A cochain whose class is parabolic is parabolic.** -/
theorem mem_parabolicSub_of_mem_parabolicClasses (ι : N →* Γ) (ρ : Representation ℂ Γ V)
    (a g₂ : N) (c : K →ₗ[ℂ] (Γ → V)) (f : K →ₗ[ℂ] H)
    (hker : ∀ x, f x = 0 → ∃ u : V, ∀ γ, c x γ = ρ γ u - u) {x : K}
    (h : f x ∈ parabolicClasses ι ρ a g₂ c f) : x ∈ parabolicSub ι ρ a g₂ c := by
  obtain ⟨x', hx', hxx⟩ := Submodule.mem_map.mp h
  have h0 : f (x - x') = 0 := by rw [map_sub, hxx, sub_self]
  obtain ⟨w, hw⟩ := hker _ h0
  have e : c x = fun γ => c x' γ + (ρ γ w - w) := by
    funext γ
    have h1 := hw γ
    rw [map_sub, Pi.sub_apply] at h1
    rw [← h1]
    abel
  obtain ⟨hc', v, hv⟩ := mem_parabolicCochains.mp (mem_parabolicSub.mp hx')
  refine mem_parabolicSub.mpr (mem_parabolicCochains.mpr ⟨?_, v + (w, w, w), ?_⟩)
  · rw [e]
    exact isCocycle_add hc' (isCocycle_boundary ρ w)
  · rw [e]
    exact isPrimitive_add hv (isPrimitive_boundary (ρ.comp ι) a g₂ w)

end Generic

namespace LevelOne

/-- A one-cocycle of `GL₂(ℤ)` whose class is parabolic is parabolic. -/
theorem mem_parabolicCocycles_of_projectH1_mem (M : Rep.{0, 0, 0} ℂ GL2Z)
    {x : groupCohomology.cocycles₁ M} (h : projectH1 M x ∈ parabolicH1 M) :
    x ∈ parabolicCocycles M :=
  mem_parabolicSub_of_mem_parabolicClasses toGL M.ρ ModularGroup.S ModularGroup.T⁻¹
    (cocycleInclusion M) (projectH1 M) (fun y h => (projectH1_eq_zero_iff M y).1 h) h

/-- A one-cocycle whose class is the negative of a parabolic class is parabolic. -/
theorem mem_parabolicCocycles_of_eq_neg (M : Rep.{0, 0, 0} ℂ GL2Z)
    {x : groupCohomology.cocycles₁ M} {E : groupCohomology.H1 M} (hE : E ∈ parabolicH1 M)
    (h : projectH1 M x = -E) : x ∈ parabolicCocycles M :=
  mem_parabolicCocycles_of_projectH1_mem M (by rw [h]; exact Submodule.neg_mem _ hE)

/-- A one-cocycle whose class is the negative of a nonzero class has nonzero class. -/
theorem projectH1_ne_zero_of_eq_neg (M : Rep.{0, 0, 0} ℂ GL2Z) {x : groupCohomology.cocycles₁ M}
    {E : groupCohomology.H1 M} (hE : E ≠ 0) (h : projectH1 M x = -E) : projectH1 M x ≠ 0 := by
  rw [h]
  exact neg_ne_zero.mpr hE

end LevelOne

namespace LevelThree

open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators GammaOneThree

/-- A crossed homomorphism of `Γ₁'(3)` whose class is parabolic is parabolic. -/
theorem mem_parabolicCrossed_of_mem {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ binaryArithmeticLevel V) {x : crossedCocycles ρ}
    (h : (crossedBoundaries ρ).mkQ x ∈ parabolicCrossedH1 ρ) : x ∈ parabolicCrossed ρ :=
  mem_parabolicSub_of_mem_parabolicClasses core.subtype ρ coreT coreL⁻¹
    (crossedCocycles ρ).subtype (crossedBoundaries ρ).mkQ
    (fun y h => (crossed_mkQ_eq_zero_iff ρ y).1 h) h

end LevelThree

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
