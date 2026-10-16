module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
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
# Averaging equivariant homomorphisms over a finite quotient

For a finite index subgroup `N ≤ K`, `K`-modules `S`, `E` over a field `k` in which `[K : N]` is
invertible, the averaging operator `Φ ↦ [K:N]⁻¹ ∑_{q ∈ K/N} q·Φ` sends `N`-equivariant linear maps
`S → E` to `K`-equivariant ones and is the identity on `K`-equivariant ones. Hence
`Hom_K(S, E) = {Φ ∈ Hom_N(S, E) : avg Φ = Φ}`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open scoped Pointwise

variable {k K : Type*} [Field k] [Group K] {S E : Type*} [AddCommGroup S] [Module k S]
  [AddCommGroup E] [Module k E] (σ : Representation k K S) (ρ : Representation k K E)

/-- `Φ` is equivariant for the subgroup `H`. -/
def IsEquivOn (H : Subgroup K) (Φ : S →ₗ[k] E) : Prop :=
  ∀ h ∈ H, ∀ z, Φ (σ h z) = ρ h (Φ z)

variable (N : Subgroup K) [N.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The summand `ρ(g) Φ(σ(g⁻¹) z)` of the averaging operator. -/
def term (Φ : S →ₗ[k] E) (g : K) (z : S) : E := ρ g (Φ (σ g⁻¹ z))

/-- The sum over a chosen set of coset representatives (before normalization). -/
def avgSum (Φ : S →ₗ[k] E) (z : S) : E := ∑ q : K ⧸ N, term σ ρ Φ q.out z

/-- The averaging operator. -/
def avg (Φ : S →ₗ[k] E) : S →ₗ[k] E where
  toFun z := ((Fintype.card (K ⧸ N) : k)⁻¹) • avgSum σ ρ N Φ z
  map_add' x y := by
    simp [avgSum, term, Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    simp [avgSum, term, Finset.smul_sum, smul_comm c]

variable {σ ρ N}

omit [N.FiniteIndex] in
theorem term_mul_right {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ N Φ) {g n : K} (hn : n ∈ N) (z : S) :
    term σ ρ Φ (g * n) z = term σ ρ Φ g z := by
  unfold term
  have h1 : σ (g * n)⁻¹ z = σ n⁻¹ (σ g⁻¹ z) := by
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [h1, hΦ n⁻¹ (N.inv_mem hn), map_mul, Module.End.mul_apply]
  rw [← Module.End.mul_apply (ρ n), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

omit [N.FiniteIndex] in
theorem term_eq_of_mk_eq {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ N Φ) {g g' : K}
    (h : (g : K ⧸ N) = g') (z : S) : term σ ρ Φ g z = term σ ρ Φ g' z := by
  obtain ⟨n, hn, rfl⟩ : ∃ n ∈ N, g' = g * n := by
    have := QuotientGroup.eq.mp h
    exact ⟨g⁻¹ * g', this, by simp⟩
  exact (term_mul_right hΦ hn z).symm

theorem term_translate (Φ : S →ₗ[k] E) (k₀ g : K) (z : S) :
    term σ ρ Φ g (σ k₀ z) = ρ k₀ (term σ ρ Φ (k₀⁻¹ * g) z) := by
  have hL : σ g⁻¹ (σ k₀ z) = σ (g⁻¹ * k₀) z := by rw [map_mul, Module.End.mul_apply]
  have hR : ∀ w, ρ k₀ (ρ (k₀⁻¹ * g) w) = ρ g w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  unfold term
  rw [hL, mul_inv_rev, inv_inv]
  exact (hR _).symm

theorem avgSum_translate {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ N Φ) (k₀ : K) (z : S) :
    avgSum σ ρ N Φ (σ k₀ z) = ρ k₀ (avgSum σ ρ N Φ z) := by
  unfold avgSum
  rw [map_sum]
  simp only [term_translate]
  let e : Equiv.Perm (K ⧸ N) := MulAction.toPerm k₀⁻¹
  rw [← Equiv.sum_comp e (fun q => ρ k₀ (term σ ρ Φ q.out z))]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply term_eq_of_mk_eq hΦ
  have h1 : ((k₀⁻¹ * q.out : K) : K ⧸ N) = k₀⁻¹ • (q.out : K ⧸ N) := rfl
  rw [h1, QuotientGroup.out_eq']
  exact (QuotientGroup.out_eq' (e q)).symm

theorem avg_isEquiv {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ N Φ) :
    IsEquivOn σ ρ ⊤ (avg σ ρ N Φ) := by
  intro k₀ _ z
  change ((Fintype.card (K ⧸ N) : k)⁻¹) • avgSum σ ρ N Φ (σ k₀ z) =
    ρ k₀ (((Fintype.card (K ⧸ N) : k)⁻¹) • avgSum σ ρ N Φ z)
  rw [avgSum_translate hΦ, map_smul]

theorem avg_of_isEquiv {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ ⊤ Φ)
    (hm : (Fintype.card (K ⧸ N) : k) ≠ 0) : avg σ ρ N Φ = Φ := by
  ext z
  change ((Fintype.card (K ⧸ N) : k)⁻¹) • avgSum σ ρ N Φ z = Φ z
  have hterm : ∀ g : K, term σ ρ Φ g z = Φ z := fun g => by
    unfold term
    rw [hΦ g⁻¹ trivial, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  simp only [avgSum, hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hm, one_smul]

theorem avg_of_isEquiv_natCard {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ ⊤ Φ)
    (hm : (Nat.card (K ⧸ N) : k) ≠ 0) : avg σ ρ N Φ = Φ :=
  avg_of_isEquiv hΦ (by rwa [← Nat.card_eq_fintype_card])

variable (σ ρ N) in
/-- The unnormalized average as a linear map. -/
def avgSumL (Φ : S →ₗ[k] E) : S →ₗ[k] E where
  toFun := avgSum σ ρ N Φ
  map_add' x y := by
    simp [avgSum, term, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [avgSum, term, Finset.smul_sum]

theorem avgSumL_eq_natCard_smul_avg (hm : (Nat.card (K ⧸ N) : k) ≠ 0) (Φ : S →ₗ[k] E) :
    avgSumL σ ρ N Φ = (Nat.card (K ⧸ N) : k) • avg σ ρ N Φ := by
  ext z
  rw [Nat.card_eq_fintype_card] at hm ⊢
  change avgSum σ ρ N Φ z = (Fintype.card (K ⧸ N) : k) •
    (((Fintype.card (K ⧸ N) : k)⁻¹) • avgSum σ ρ N Φ z)
  rw [smul_smul, mul_inv_cancel₀ hm, one_smul]

variable (σ ρ) in
/-- The action `Φ ↦ ρ(g) ∘ Φ ∘ σ(g⁻¹)` of `g ∈ K` on linear maps. -/
def actL (g : K) (Φ : S →ₗ[k] E) : S →ₗ[k] E := ρ g ∘ₗ Φ ∘ₗ σ g⁻¹

theorem actL_apply (g : K) (Φ : S →ₗ[k] E) (z : S) : actL σ ρ g Φ z = term σ ρ Φ g z := rfl

theorem avgSumL_eq_sum (Φ : S →ₗ[k] E) :
    avgSumL σ ρ N Φ = ∑ q : K ⧸ N, actL σ ρ q.out Φ := by
  ext z
  change avgSum σ ρ N Φ z = _
  simp [avgSum, LinearMap.sum_apply, actL_apply]

theorem avg_eq_sum (Φ : S →ₗ[k] E) :
    avg σ ρ N Φ = ((Fintype.card (K ⧸ N) : k)⁻¹) • ∑ q : K ⧸ N, actL σ ρ q.out Φ := by
  ext z
  simp [avg, avgSum, LinearMap.sum_apply, actL_apply]

end TernaryPeriodPolynomials.Argument.GroupHomology
