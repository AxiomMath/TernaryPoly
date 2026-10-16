module

public import TernaryPeriodPolynomials.Building.Path.Class

@[expose] public section


/-! A fixed vertex kills the restricted path class for every original path family. -/

noncomputable section
open CategoryTheory

namespace TernaryPeriodPolynomial.PathCocycle.BoundaryData

variable {G : Type} {C₁ C₀ : Type*} [Group G]
  [AddCommGroup C₁] [Module ℚ C₁] [AddCommGroup C₀] [Module ℚ C₀]
  {D : BoundaryData G C₁ C₀} {v : C₀}

namespace Paths

/-- Adapt paths on a subgroup using a chain from the base to its fixed vertex. -/
def adaptedAtFixedVertex (τ : D.Paths v) (H : Subgroup G) (w : C₀) (s : C₁)
    (hs : D.boundary s = v - w) (hw : ∀ g ∈ H, D.vertices g w = w) : D.Paths v := by
  classical
  refine { path := fun g => if g ∈ H then s - D.chains g s else τ.path g
           boundary_path := ?_ }
  intro g
  by_cases hg : g ∈ H
  · rw [ite_eq_left hg, map_sub, D.equivariant, hs, map_sub, hw g hg]
    abel
  · rw [ite_eq_right hg]
    exact τ.boundary_path g

/-- On the fixing subgroup the adapted family comes from one actual chain. -/
theorem adaptedAtFixedVertex_apply_of_mem (τ : D.Paths v) (H : Subgroup G)
    (w : C₀) (s : C₁) (hs : D.boundary s = v - w)
    (hw : ∀ g ∈ H, D.vertices g w = w) (g : G) (hg : g ∈ H) :
    (τ.adaptedAtFixedVertex H w s hs hw).path g = s - D.chains g s := by
  classical
  exact ite_eq_left hg

/-- Outside the subgroup the original paths are retained. -/
theorem adaptedAtFixedVertex_apply_of_notMem (τ : D.Paths v) (H : Subgroup G)
    (w : C₀) (s : C₁) (hs : D.boundary s = v - w)
    (hw : ∀ g ∈ H, D.vertices g w = w) (g : G) (hg : g ∉ H) :
    (τ.adaptedAtFixedVertex H w s hs hw).path g = τ.path g := by
  classical
  exact ite_eq_right hg

end Paths

namespace CycleMap

variable {E : Type} [AddCommGroup E] [Module ℚ E] (F : D.CycleMap E)

/-- The original cocycle on the fixing subgroup has an explicit coboundary witness. -/
theorem cocycle_eq_coboundary_of_fixed_vertex (τ : D.Paths v) (H : Subgroup G)
    (w : C₀) (s : C₁) (hs : D.boundary s = v - w)
    (hw : ∀ g ∈ H, D.vertices g w = w)
    (g h : G) (hg : g ∈ H) (hh : h ∈ H) :
    F.cocycle τ g h =
      F.coboundary (F.changeCochain (τ.adaptedAtFixedVertex H w s hs hw) τ) g h := by
  have hc := F.cocycle_sub (τ.adaptedAtFixedVertex H w s hs hw) τ g h
  rw [F.cocycle_eq_zero_on_subgroup (τ.adaptedAtFixedVertex H w s hs hw) H s
    (τ.adaptedAtFixedVertex_apply_of_mem H w s hs hw) g h hg hh, sub_zero] at hc
  exact hc

/-- Actual group-cohomological restriction vanishes on a subgroup fixing a reachable vertex. -/
theorem pathClass_restrict_eq_zero_of_fixed_vertex (τ : D.Paths v) (H : Subgroup G)
    (w : C₀) (s : C₁) (hs : D.boundary s = v - w)
    (hw : ∀ g ∈ H, D.vertices g w = w) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.of F.action))) 2
      (F.pathClass τ) = 0 := by
  rw [← F.pathClass_independent τ (τ.adaptedAtFixedVertex H w s hs hw)]
  exact F.pathClass_restrict_eq_zero (τ.adaptedAtFixedVertex H w s hs hw) H s
    (τ.adaptedAtFixedVertex_apply_of_mem H w s hs hw)

end CycleMap
end TernaryPeriodPolynomial.PathCocycle.BoundaryData
