module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ModuleClasses
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section


/-! Cyclewise boundary criteria for the actual module homology map. -/
noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory HomologicalComplex

variable {R : Type} [Ring R]

theorem moduleHomologyMap_eq_zero_of_boundaries
    {S T : ShortComplex (ModuleCat.{0} R)} (f : S ⟶ T)
    (h : ∀ x : S.X₂, S.g.hom x = 0 → f.τ₂.hom x ∈ LinearMap.range T.f.hom) :
    ShortComplex.homologyMap f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x,hx,rfl⟩ := moduleClass_surjective S z
  change ShortComplex.homologyMap f (moduleClass S x hx) = 0
  rw [moduleClass_natural, moduleClass_eq_zero_iff]
  exact h x hx

theorem cochainHomologyMap_eq_zero_of_boundaries
    {A B : CochainComplex (ModuleCat.{0} R) ℕ} (f : A ⟶ B) (n : ℕ)
    (h : ∀ x : A.X n, (A.d n (n+1)).hom x = 0 →
      ∃ y : B.X (n-1), (B.d (n-1) n).hom y = (f.f n).hom x) :
    homologyMap f n = 0 := by
  apply moduleHomologyMap_eq_zero_of_boundaries
  intro x hx
  have hp : (ComplexShape.up ℕ).prev n = n-1 := by
    cases n <;> simp
  change (A.d n ((ComplexShape.up ℕ).next n)).hom x = 0 at hx
  rw [CochainComplex.next] at hx
  change (f.f n).hom x ∈ LinearMap.range (B.d ((ComplexShape.up ℕ).prev n) n).hom
  rw [hp]
  exact h x hx

end TernaryPoly.SmoothSingularGlobal
