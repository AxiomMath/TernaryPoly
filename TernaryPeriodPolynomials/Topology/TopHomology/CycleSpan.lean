module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Linear algebra of a one-dimensional top cohomology

For vector spaces `C₅ →d₅ C₄ →d₄ C₃` over a field `K` (with `d₄ ∘ d₅ = 0`), if the space of
cocycles `{φ : C₄ → K | φ ∘ d₅ = 0}` modulo coboundaries `{η ∘ d₄}` has dimension at most one
(`CohomologyAtMostOne`), then the cycles `ker d₄` are spanned by one cycle `ω` modulo boundaries
`range d₅` (`exists_cycle_span`), and a cocycle with values in any `K`-vector space `W` that vanishes
on `ω` is a coboundary (`cocycle_eq_comp_of_apply_eq_zero`).  This is the universal-coefficient
mechanism used to pass from the rational coefficients of Poincaré duality to complex coefficients.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

variable {K : Type*} [Field K] {C₅ C₄ C₃ : Type*} [AddCommGroup C₅] [Module K C₅]
  [AddCommGroup C₄] [Module K C₄] [AddCommGroup C₃] [Module K C₃]
  (d₅ : C₅ →ₗ[K] C₄) (d₄ : C₄ →ₗ[K] C₃)

/-- Any two cocycles of `Hom(C, K)` in degree four are dependent modulo coboundaries. -/
def CohomologyAtMostOne : Prop :=
  ∀ φ₁ φ₂ : C₄ →ₗ[K] K, φ₁ ∘ₗ d₅ = 0 → φ₂ ∘ₗ d₅ = 0 →
    ∃ (a b : K) (η : C₃ →ₗ[K] K), (a ≠ 0 ∨ b ≠ 0) ∧ a • φ₁ + b • φ₂ = η ∘ₗ d₄

variable {d₅ d₄}

/-- Cycles are spanned by a single cycle modulo boundaries. -/
theorem exists_cycle_span (h : CohomologyAtMostOne d₅ d₄) :
    ∃ ω : C₄, d₄ ω = 0 ∧ ∀ z : C₄, d₄ z = 0 → ∃ c : K, z - c • ω ∈ LinearMap.range d₅ := by
  by_cases hall : ∀ z : C₄, d₄ z = 0 → z ∈ LinearMap.range d₅
  · exact ⟨0, map_zero _, fun z hz => ⟨0, by simpa using hall z hz⟩⟩
  · push Not at hall
    obtain ⟨z₀, hz₀, hz₀B⟩ := hall
    refine ⟨z₀, hz₀, fun z hz => ?_⟩
    by_contra hcon
    push Not at hcon
    set B := LinearMap.range d₅ with hB
    have hz₀1 : z₀ ∉ B ⊔ Submodule.span K {z} := by
      intro hmem
      obtain ⟨b, hb, y, hy, hsum⟩ := Submodule.mem_sup.mp hmem
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      by_cases hc : c = 0
      · subst hc
        apply hz₀B
        simpa [← hsum] using hb
      · apply hcon c⁻¹
        have : z - c⁻¹ • z₀ = (-c⁻¹) • b := by
          rw [← hsum, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
          module
        rw [this]
        exact B.smul_mem _ hb
    have hz1 : z ∉ B ⊔ Submodule.span K {z₀} := by
      intro hmem
      obtain ⟨b, hb, y, hy, hsum⟩ := Submodule.mem_sup.mp hmem
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      apply hcon c
      have : z - c • z₀ = b := by rw [← hsum]; abel
      rw [this]
      exact hb
    obtain ⟨f₁, hf₁, hBf₁⟩ := Submodule.exists_le_ker_of_notMem hz₀1
    obtain ⟨f₂, hf₂, hBf₂⟩ := Submodule.exists_le_ker_of_notMem hz1
    have hf₁B : ∀ x ∈ B, f₁ x = 0 := fun x hx =>
      LinearMap.mem_ker.mp (hBf₁ (Submodule.mem_sup_left hx))
    have hf₂B : ∀ x ∈ B, f₂ x = 0 := fun x hx =>
      LinearMap.mem_ker.mp (hBf₂ (Submodule.mem_sup_left hx))
    have hf₁z : f₁ z = 0 :=
      LinearMap.mem_ker.mp (hBf₁ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)))
    have hf₂z₀ : f₂ z₀ = 0 :=
      LinearMap.mem_ker.mp (hBf₂ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z₀)))
    obtain ⟨a, b, η, hab, heq⟩ := h f₁ f₂
      (LinearMap.ext fun x => hf₁B _ ⟨x, rfl⟩) (LinearMap.ext fun x => hf₂B _ ⟨x, rfl⟩)
    have e1 := LinearMap.congr_fun heq z₀
    have e2 := LinearMap.congr_fun heq z
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, hz₀, hz,
      map_zero, hf₂z₀, hf₁z, mul_zero, add_zero, zero_add] at e1 e2
    rcases hab with ha | hb
    · exact ha ((mul_eq_zero.mp e1).resolve_right hf₁)
    · exact hb ((mul_eq_zero.mp e2).resolve_right hf₂)

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- A cocycle vanishing on the spanning cycle is a coboundary. -/
theorem cocycle_eq_comp_of_apply_eq_zero {ω : C₄}
    (hω : ∀ z : C₄, d₄ z = 0 → ∃ c : K, z - c • ω ∈ LinearMap.range d₅)
    (φ : C₄ →ₗ[K] W) (hφ : φ ∘ₗ d₅ = 0) (hω0 : φ ω = 0) :
    ∃ η : C₃ →ₗ[K] W, φ = η ∘ₗ d₄ := by
  have hker : LinearMap.ker d₄ ≤ LinearMap.ker φ := by
    intro z hz
    obtain ⟨c, y, hy⟩ := hω z (LinearMap.mem_ker.mp hz)
    have : z = c • ω + d₅ y := by rw [hy]; abel
    rw [LinearMap.mem_ker, this, map_add, map_smul, hω0, smul_zero, zero_add]
    exact LinearMap.congr_fun hφ y
  let ψ₀ : LinearMap.range d₄ →ₗ[K] W :=
    ((LinearMap.ker d₄).liftQ φ hker) ∘ₗ d₄.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ψ₀
  refine ⟨g, LinearMap.ext fun x => ?_⟩
  have := LinearMap.congr_fun hg ⟨d₄ x, LinearMap.mem_range_self d₄ x⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [LinearMap.comp_apply, this]
  simp only [ψ₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearMap.quotKerEquivRange_symm_apply_image d₄ x]
  rfl

end TernaryPeriodPolynomials.Argument.TopHomology
