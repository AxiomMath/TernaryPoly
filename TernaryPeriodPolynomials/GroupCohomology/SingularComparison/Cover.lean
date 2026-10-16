module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Homology of a module complex covered by a complex of modules

Formalized by Claude Sonnet 5.5.

For a short complex of modules `S : X₁ → X₂ → X₃` covered by surjections `σᵢ : Mᵢ → Xᵢ` (`i = 1, 2`) with
`f σ₁ = σ₂ ∂₁` and `g σ₂ = σ₃ ∂₂` (`σ₃` arbitrary), the homology of `S` is the quotient of
`Z = {m ∈ M₂ | ∂₂ m ∈ ker σ₃}` by `ker σ₂ ⊔ ∂₁ M₁`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory

universe v

section Cover

variable (S : ShortComplex (ModuleCat.{v} ℂ)) {M₁ M₂ M₃ : Type v}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  (σ₁ : M₁ →ₗ[ℂ] S.X₁) (σ₂ : M₂ →ₗ[ℂ] S.X₂) (σ₃ : M₃ →ₗ[ℂ] S.X₃)
  (d₁ : M₁ →ₗ[ℂ] M₂) (d₂ : M₂ →ₗ[ℂ] M₃)

/-- The "cycles modulo the kernel of the covering": `{m | ∂₂ m ∈ ker σ₃}`. -/
def coverCycles (σ₃ : M₃ →ₗ[ℂ] S.X₃) (d₂ : M₂ →ₗ[ℂ] M₃) : Submodule ℂ M₂ :=
  (LinearMap.ker σ₃).comap d₂

variable {S σ₁ σ₂ σ₃ d₁ d₂}

theorem cover_mem_ker (h₂ : ∀ m, S.g.hom (σ₂ m) = σ₃ (d₂ m)) {m : M₂}
    (hm : m ∈ coverCycles S σ₃ d₂) : σ₂ m ∈ LinearMap.ker S.g.hom := by
  rw [LinearMap.mem_ker, h₂]
  exact hm

/-- The class of a covering cycle in the homology of `S`. -/
def coverClass (h₂ : ∀ m, S.g.hom (σ₂ m) = σ₃ (d₂ m)) : coverCycles S σ₃ d₂ →ₗ[ℂ] S.homology :=
  (S.moduleCatHomologyIso.inv.hom ∘ₗ (Submodule.mkQ _)) ∘ₗ
    (σ₂.restrict (fun _ hm => cover_mem_ker h₂ hm))

theorem coverClass_surjective (h₂ : ∀ m, S.g.hom (σ₂ m) = σ₃ (d₂ m))
    (hσ₂ : Function.Surjective σ₂) : Function.Surjective (coverClass h₂) := by
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective S.moduleCatHomologyIso.inv).mp inferInstance x
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨m, hm⟩ := hσ₂ c.1
  have hmz : m ∈ coverCycles S σ₃ d₂ := by
    have := c.2
    rw [LinearMap.mem_ker, ← hm, h₂] at this
    exact this
  refine ⟨⟨m, hmz⟩, ?_⟩
  rw [← hy]
  change S.moduleCatHomologyIso.inv.hom (Submodule.mkQ _ ⟨σ₂ m, _⟩) = _
  congr 2
  exact Subtype.ext hm

theorem coverClass_eq_zero_iff (h₁ : ∀ m, S.f.hom (σ₁ m) = σ₂ (d₁ m))
    (h₂ : ∀ m, S.g.hom (σ₂ m) = σ₃ (d₂ m)) (hσ₁ : Function.Surjective σ₁)
    (m : coverCycles S σ₃ d₂) :
    coverClass h₂ m = 0 ↔ (m : M₂) ∈ LinearMap.ker σ₂ ⊔ LinearMap.range d₁ := by
  have hiso : coverClass h₂ m = 0 ↔
      Submodule.mkQ (LinearMap.range S.moduleCatToCycles)
        ⟨σ₂ m, cover_mem_ker h₂ m.2⟩ = 0 := by
    change S.moduleCatHomologyIso.inv.hom _ = 0 ↔ _
    rw [← map_zero S.moduleCatHomologyIso.inv.hom]
    exact (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.inv).mp inferInstance |>.eq_iff
  rw [hiso, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hσ₁ x
    have hx' : S.f.hom (σ₁ y) = σ₂ m := congrArg Subtype.val hx
    rw [h₁] at hx'
    refine Submodule.mem_sup.mpr ⟨(m : M₂) - d₁ y, ?_, d₁ y, ⟨y, rfl⟩, by abel⟩
    rw [LinearMap.mem_ker, map_sub, ← hx', sub_self]
  · intro h
    obtain ⟨a, ha, b, ⟨y, rfl⟩, hab⟩ := Submodule.mem_sup.mp h
    refine ⟨σ₁ y, ?_⟩
    apply Subtype.ext
    change S.f.hom (σ₁ y) = σ₂ m
    rw [h₁, ← hab, map_add, LinearMap.mem_ker.mp ha, zero_add]

theorem coverClass_eq_homologyπ (h₂ : ∀ m, S.g.hom (σ₂ m) = σ₃ (d₂ m)) (m : coverCycles S σ₃ d₂) :
    coverClass h₂ m = S.homologyπ (S.moduleCatCyclesIso.inv ⟨σ₂ m, cover_mem_ker h₂ m.2⟩) := by
  have h := ShortComplex.moduleCatCyclesIso_inv_π (S := S)
  have h' := congrArg (fun t => t.hom ⟨σ₂ m, cover_mem_ker h₂ m.2⟩) h
  exact h'.symm

end Cover

section Natural

variable {S S' : ShortComplex (ModuleCat.{v} ℂ)} (φ : S ⟶ S') {M₂ M₃ : Type v}
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  {σ₂ : M₂ →ₗ[ℂ] S.X₂} {σ₂' : M₂ →ₗ[ℂ] S'.X₂} {σ₃ : M₃ →ₗ[ℂ] S.X₃} {σ₃' : M₃ →ₗ[ℂ] S'.X₃}
  {d₂ : M₂ →ₗ[ℂ] M₃}

theorem coverCycles_mono (hσ₃ : ∀ m, φ.τ₃.hom (σ₃ m) = σ₃' m) :
    coverCycles S σ₃ d₂ ≤ coverCycles S' σ₃' d₂ := by
  intro m hm
  change σ₃' (d₂ m) = 0
  rw [← hσ₃]
  change σ₃ (d₂ m) = 0 at hm
  rw [hm, map_zero]

theorem coverClass_natural (hσ₂ : ∀ m, φ.τ₂.hom (σ₂ m) = σ₂' m)
    (hσ₃ : ∀ m, φ.τ₃.hom (σ₃ m) = σ₃' m)
    (h₂ : ∀ m, S.g.hom (σ₂ m) = σ₃ (d₂ m)) (h₂' : ∀ m, S'.g.hom (σ₂' m) = σ₃' (d₂ m))
    (m : coverCycles S σ₃ d₂) :
    (ShortComplex.homologyMap φ).hom (coverClass h₂ m) =
      coverClass h₂' ⟨m.1, coverCycles_mono φ hσ₃ m.2⟩ := by
  rw [coverClass_eq_homologyπ h₂, coverClass_eq_homologyπ h₂']
  have e1 := ShortComplex.homologyπ_naturality φ
  have e2 := congrArg (fun t => t.hom (S.moduleCatCyclesIso.inv ⟨σ₂ m, cover_mem_ker h₂ m.2⟩)) e1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e2
  have e3 : (ShortComplex.cyclesMap φ).hom (S.moduleCatCyclesIso.inv ⟨σ₂ m, cover_mem_ker h₂ m.2⟩) =
      S'.moduleCatCyclesIso.inv ⟨σ₂' m, cover_mem_ker h₂' (coverCycles_mono φ hσ₃ m.2)⟩ := by
    apply (ModuleCat.mono_iff_injective S'.iCycles).mp inferInstance
    have a1 := congrArg (fun t => t.hom (S.moduleCatCyclesIso.inv ⟨σ₂ m, cover_mem_ker h₂ m.2⟩))
      (ShortComplex.cyclesMap_i φ)
    have a2 := congrArg (fun t => t.hom ⟨σ₂ m, cover_mem_ker h₂ m.2⟩)
      (ShortComplex.moduleCatCyclesIso_inv_iCycles (S := S))
    have a3 := congrArg (fun t => t.hom ⟨σ₂' m, cover_mem_ker h₂' (coverCycles_mono φ hσ₃ m.2)⟩)
      (ShortComplex.moduleCatCyclesIso_inv_iCycles (S := S'))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at a1 a2 a3
    have a2' : (S.iCycles.hom (S.moduleCatCyclesIso.inv.hom ⟨σ₂ m, cover_mem_ker h₂ m.2⟩)) = σ₂ m := a2
    have a3' : (S'.iCycles.hom (S'.moduleCatCyclesIso.inv.hom
        ⟨σ₂' m, cover_mem_ker h₂' (coverCycles_mono φ hσ₃ m.2)⟩)) = σ₂' m := a3
    rw [a3']
    change S'.iCycles.hom ((ShortComplex.cyclesMap φ).hom _) = _
    rw [a1, a2', hσ₂]
  rw [← e3]
  exact e2

end Natural

end TernaryPeriodPolynomials.Argument.HomologyBridge
