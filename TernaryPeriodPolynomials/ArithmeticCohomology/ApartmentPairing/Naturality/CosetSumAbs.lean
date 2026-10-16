module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Summing over cosets of a smaller normal subgroup (abstract)

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open scoped Classical

section Abstract

variable {G : Type*} [Group G] (K : Subgroup G) (N : Subgroup G) [N.Normal] (NK : Subgroup K) [NK.Normal]

/-- The inclusion of coset spaces `K/N_K → G/N`. -/
def cosetIncl (hNK : ∀ k : K, k ∈ NK ↔ (k : G) ∈ N) : K ⧸ NK → G ⧸ N :=
  QuotientGroup.map NK N K.subtype (fun k hk => (hNK k).mp hk)

theorem cosetIncl_mk (hNK : ∀ k : K, k ∈ NK ↔ (k : G) ∈ N) (k : K) :
    cosetIncl K N NK hNK (QuotientGroup.mk k) = QuotientGroup.mk (k : G) := rfl

theorem cosetIncl_injective (hNK : ∀ k : K, k ∈ NK ↔ (k : G) ∈ N) :
    Function.Injective (cosetIncl K N NK hNK) := by
  intro a b h
  induction a using QuotientGroup.induction_on with | H a =>
  induction b using QuotientGroup.induction_on with | H b =>
  rw [cosetIncl_mk, cosetIncl_mk, QuotientGroup.eq] at h
  rw [QuotientGroup.eq, hNK]
  simpa using h

theorem sum_quot_eq (hNK : ∀ k : K, k ∈ NK ↔ (k : G) ∈ N) [Fintype (G ⧸ N)] [Fintype (K ⧸ NK)]
    {W : Type*} [AddCommMonoid W] (F : G → W) (hinv : ∀ (g n : G), n ∈ N → F (g * n) = F g)
    (hsupp : ∀ g, g ∉ K → F g = 0) :
    ∑ q : G ⧸ N, F q.out = ∑ q' : K ⧸ NK, F ((q'.out : K) : G) := by
  symm
  refine Fintype.sum_of_injective (cosetIncl K N NK hNK) (cosetIncl_injective K N NK hNK)
    (fun q' => F ((q'.out : K) : G)) (fun q => F q.out) ?_ ?_
  · intro i hi
    by_cases hk : (i.out : G) ∈ K
    · exfalso
      apply hi
      refine ⟨QuotientGroup.mk ⟨i.out, hk⟩, ?_⟩
      rw [cosetIncl_mk]
      exact QuotientGroup.out_eq' i
    · exact hsupp _ hk
  · intro q'
    have h1 : (QuotientGroup.mk (((cosetIncl K N NK hNK q').out : G)) : G ⧸ N) =
        cosetIncl K N NK hNK q' := QuotientGroup.out_eq' _
    have h2 : cosetIncl K N NK hNK q' = (QuotientGroup.mk (((q'.out : K) : G)) : G ⧸ N) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q']
      rfl
    have h4 : (QuotientGroup.mk (((cosetIncl K N NK hNK q').out : G)) : G ⧸ N) =
        QuotientGroup.mk (((q'.out : K) : G)) := h1.trans h2
    rw [QuotientGroup.eq] at h4
    have h5 := hinv ((cosetIncl K N NK hNK q').out : G) _ h4
    rw [mul_inv_cancel_left] at h5
    exact h5

omit [N.Normal] [NK.Normal] in
theorem card_quot_mul (hNK : ∀ k : K, k ∈ NK ↔ (k : G) ∈ N) (hN : N ≤ K) :
    Nat.card (G ⧸ N) = Nat.card (G ⧸ K) * Nat.card (K ⧸ NK) := by
  have h1 : NK = N.subgroupOf K := by
    ext k; rw [hNK, Subgroup.mem_subgroupOf]
  have h2 := Subgroup.relIndex_mul_index hN
  rw [Subgroup.relIndex, ← h1] at h2
  change Nat.card (K ⧸ NK) * Nat.card (G ⧸ K) = Nat.card (G ⧸ N) at h2
  rw [← h2, mul_comm]

end Abstract


end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
