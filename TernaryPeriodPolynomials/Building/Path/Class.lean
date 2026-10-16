module

public import TernaryPeriodPolynomials.Building.Path.Cocycle
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section


/-!
# The cohomology class of a path defect

The cocycle constructed from actual chains in `PathCocycle` defines an element
of Mathlib's group cohomology. Its class is independent of the chosen paths.
-/

noncomputable section

open CategoryTheory

namespace TernaryPeriodPolynomial.PathCocycle.BoundaryData.CycleMap

variable {G E : Type} {C₁ C₀ : Type*} [Group G]
  [AddCommGroup C₁] [Module ℚ C₁] [AddCommGroup C₀] [Module ℚ C₀]
  [AddCommGroup E] [Module ℚ E]
  {D : BoundaryData G C₁ C₀} (F : D.CycleMap E) {v : C₀}

/-- The path-defect cocycle as an element of Mathlib's module of 2-cocycles. -/
def bundledCocycle (τ : D.Paths v) : groupCohomology.cocycles₂ (Rep.of F.action) :=
  ⟨fun gh => F.cocycle τ gh.1 gh.2, by
    apply (groupCohomology.mem_cocycles₂_def _).2
    exact F.cocycle_condition τ⟩

@[simp] theorem bundledCocycle_apply (τ : D.Paths v) (g h : G) :
    F.bundledCocycle τ (g, h) = F.cocycle τ g h := rfl

/-- The class of the path-defect cocycle in actual degree-two group cohomology. -/
def pathClass (τ : D.Paths v) : groupCohomology.H2 (Rep.of F.action) :=
  groupCohomology.H2π (Rep.of F.action) (F.bundledCocycle τ)

/-- The difference of two path-defect cocycles belongs to the actual coboundary module. -/
theorem bundledCocycle_sub_mem_coboundaries (τ σ : D.Paths v) :
    ⇑(F.bundledCocycle σ) - ⇑(F.bundledCocycle τ) ∈
      groupCohomology.coboundaries₂ (Rep.of F.action) := by
  change ∃ b : G → E, (groupCohomology.d₁₂ (Rep.of F.action)).hom b = _
  refine ⟨F.changeCochain τ σ, ?_⟩
  funext gh
  exact (F.cocycle_sub τ σ gh.1 gh.2).symm

/-- The degree-two cohomology class does not depend on the path family. -/
theorem pathClass_independent (τ σ : D.Paths v) : F.pathClass σ = F.pathClass τ := by
  exact (groupCohomology.H2π_eq_iff _ _).2 (F.bundledCocycle_sub_mem_coboundaries τ σ)

/-- The actual cohomological restriction vanishes when the subgroup paths come from one chain. -/
theorem pathClass_restrict_eq_zero (τ : D.Paths v) (H : Subgroup G) (s : C₁)
    (hpath : ∀ g ∈ H, τ.path g = s - D.chains g s) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.of F.action))) 2
      (F.pathClass τ) = 0 := by
  rw [pathClass, groupCohomology.H2π_comp_map_apply]
  have hz : groupCohomology.mapCocycles₂ H.subtype
      (𝟙 (Rep.res H.subtype (Rep.of F.action))) (F.bundledCocycle τ) = 0 := by
    apply groupCohomology.cocycles₂_ext
    intro g h
    change F.cocycle τ g h = 0
    exact F.cocycle_eq_zero_on_subgroup τ H s hpath g h g.property h.property
  rw [hz, map_zero]

end TernaryPeriodPolynomial.PathCocycle.BoundaryData.CycleMap
