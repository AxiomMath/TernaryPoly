module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
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
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Coinvariants and invariants of a finite quotient action, via the averaging projector (abstract)

Formalized by Claude Sonnet 5.5.

Let `ρ` be a representation of a group `Γ` over a field of characteristic `0` and `N ⊴ Γ` a finite-index normal subgroup acting
trivially.  The averaging projector `avgR ρ N = [Γ:N]⁻¹ ∑_{q ∈ Γ/N} ρ(q)` is idempotent with image the invariants, its kernel is the
kernel of the quotient map to the coinvariants, and it induces a linear isomorphism `Coinvariants ρ ≃ invariants ρ` (rational averaging).
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open Representation
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Abs

variable {k : Type*} [Field k] [CharZero k] {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal] [N.FiniteIndex]
  {B : Type*} [AddCommGroup B] [Module k B] (ρ : Representation k Γ B)

/-- The averaging operator over `Γ/N`. -/
def avgR : B →ₗ[k] B := ((Fintype.card (Γ ⧸ N) : k)⁻¹) • ∑ q : Γ ⧸ N, ρ q.out

omit [N.Normal] in
theorem card_ne_zero_R : (Fintype.card (Γ ⧸ N) : k) ≠ 0 := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero

variable {N ρ}

omit [CharZero k] [N.Normal] [N.FiniteIndex] in
theorem rho_eq_of_mk_eq (hN : ∀ n ∈ N, ρ n = 1) {g g' : Γ} (h : (g : Γ ⧸ N) = g') : ρ g = ρ g' := by
  have h1 : g⁻¹ * g' ∈ N := QuotientGroup.eq.mp h
  have h2 : g' = g * (g⁻¹ * g') := by simp
  rw [h2, map_mul, hN _ h1, mul_one]

omit [CharZero k] [N.Normal] in
theorem rho_left (hN : ∀ n ∈ N, ρ n = 1) (h : Γ) : ρ h * avgR N ρ = avgR N ρ := by
  unfold avgR
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  have : ∀ q : Γ ⧸ N, ρ h * ρ q.out = ρ ((h • q : Γ ⧸ N).out) := fun q => by
    rw [← map_mul]
    refine rho_eq_of_mk_eq hN ?_
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simp_rw [this]
  exact Equiv.sum_comp (MulAction.toPerm h) (fun q : Γ ⧸ N => ρ q.out)

omit [CharZero k] in
theorem rho_right (hN : ∀ n ∈ N, ρ n = 1) (h : Γ) : avgR N ρ * ρ h = avgR N ρ := by
  unfold avgR
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  have : ∀ q : Γ ⧸ N, ρ q.out * ρ h = ρ ((q * (h : Γ ⧸ N)).out) := fun q => by
    rw [← map_mul]
    refine rho_eq_of_mk_eq hN ?_
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  simp_rw [this]
  exact Equiv.sum_comp (Equiv.mulRight (h : Γ ⧸ N)) (fun q : Γ ⧸ N => ρ q.out)

omit [N.Normal] in
theorem avgR_idem (hN : ∀ n ∈ N, ρ n = 1) : avgR N ρ * avgR N ρ = avgR N ρ := by
  conv_lhs => arg 1; unfold avgR
  rw [smul_mul_assoc, Finset.sum_mul]
  have : ∀ q : Γ ⧸ N, ρ q.out * avgR N ρ = avgR N ρ := fun q => rho_left hN _
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ (card_ne_zero_R N), one_smul]

omit [N.Normal] in
theorem avgR_of_invariant {v : B} (hv : ∀ g, ρ g v = v) : avgR N ρ v = v := by
  unfold avgR
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ (card_ne_zero_R N), one_smul]

omit [CharZero k] [N.Normal] in
theorem avgR_invariant (hN : ∀ n ∈ N, ρ n = 1) (v : B) (g : Γ) : ρ g (avgR N ρ v) = avgR N ρ v := by
  have := rho_left hN g
  exact LinearMap.congr_fun this v

omit [N.Normal] in
theorem mk_avgR (v : B) : Coinvariants.mk ρ (avgR N ρ v) = Coinvariants.mk ρ v := by
  unfold avgR
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Coinvariants.mk_self_apply,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ (card_ne_zero_R N), one_smul]

/-- The kernel of the quotient map to the coinvariants is the kernel of the averaging operator. -/
theorem mk_eq_zero_iff_avgR (hN : ∀ n ∈ N, ρ n = 1) (v : B) :
    Coinvariants.mk ρ v = 0 ↔ avgR N ρ v = 0 := by
  constructor
  · intro h
    rw [Coinvariants.mk_eq_zero] at h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, y⟩, rfl⟩ := hx
      have h2 := LinearMap.congr_fun (rho_right hN g) y
      change avgR N ρ (ρ g y) = avgR N ρ y at h2
      simp [map_sub, h2]
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_smul, hx]
  · intro h
    rw [← mk_avgR (N := N), h, map_zero]

end Abs


end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
