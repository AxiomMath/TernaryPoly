module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.HomAveraging
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.CosetSumAbs

@[expose] public section


/-!
# Averaging over `G/N` factors through `G/H` and `H/N`

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.Naturality

open TernaryPeriodPolynomials.Argument.GroupHomology
open scoped Classical
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Tower

variable {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G] {S E : Type*} [AddCommGroup S] [Module k S]
  [AddCommGroup E] [Module k E] (σ : Representation k G S) (ρ : Representation k G E)

omit [CharZero k] in
theorem actL_mul (g h : G) (Φ : S →ₗ[k] E) : actL σ ρ (g * h) Φ = actL σ ρ g (actL σ ρ h Φ) := by
  ext z
  simp only [actL, LinearMap.comp_apply, map_mul, mul_inv_rev, Module.End.mul_apply]

omit [CharZero k] in
theorem actL_smul (g : G) (c : k) (Φ : S →ₗ[k] E) : actL σ ρ g (c • Φ) = c • actL σ ρ g Φ := by
  ext z
  simp [actL]

omit [CharZero k] in
theorem actL_sum {ι : Type*} (g : G) (s : Finset ι) (Φ : ι → (S →ₗ[k] E)) :
    actL σ ρ g (∑ i ∈ s, Φ i) = ∑ i ∈ s, actL σ ρ g (Φ i) := by
  ext z
  simp [actL, LinearMap.sum_apply]

omit [CharZero k] in
theorem actL_eq_of_mk_eq (N : Subgroup G) [N.Normal] {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ N Φ) (g : G) :
    actL σ ρ (QuotientGroup.mk g : G ⧸ N).out Φ = actL σ ρ g Φ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g
  rw [hh, actL_mul]
  congr 1
  ext z
  simp only [actL, LinearMap.comp_apply]
  rw [hΦ h⁻¹ (N.inv_mem h.2), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

variable (N H : Subgroup G) [N.Normal] [N.FiniteIndex] [H.FiniteIndex]

/-- **The average over `G/N` factors through `G/H` and `H/N`** (for `N ≤ H` and `N`-equivariant `Φ`):
`avg_{G/N} Φ = [G:H]⁻¹ ∑_{r ∈ G/H} r · avg_{H/N} Φ`. -/
theorem avg_tower (hNH : N ≤ H) [(N.subgroupOf H).Normal] [(N.subgroupOf H).FiniteIndex]
    {Φ : S →ₗ[k] E} (hΦ : IsEquivOn σ ρ N Φ) :
    avg σ ρ N Φ = ((Fintype.card (G ⧸ H) : k)⁻¹) •
      ∑ r : G ⧸ H, actL σ ρ r.out (avg (σ.comp H.subtype) (ρ.comp H.subtype) (N.subgroupOf H) Φ) := by
  have hcard : Fintype.card (G ⧸ N) = Fintype.card (G ⧸ H) * Fintype.card (↥H ⧸ N.subgroupOf H) := by
    have := card_quot_mul H N (N.subgroupOf H) (fun k => Subgroup.mem_subgroupOf) hNH
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have hG : (Fintype.card (G ⧸ H) : k) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hH : (Fintype.card (↥H ⧸ N.subgroupOf H) : k) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hsum : ∑ q : G ⧸ N, actL σ ρ q.out Φ =
      ∑ r : G ⧸ H, ∑ k' : ↥H ⧸ N.subgroupOf H, actL σ ρ (r.out * ((k'.out : ↥H) : G)) Φ := by
    rw [← Finset.sum_product']
    refine (Equiv.sum_comp (Subgroup.quotientEquivProdOfLE hNH).symm
      (fun q => actL σ ρ q.out Φ)).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨r, k'⟩ := p
    have he : (Subgroup.quotientEquivProdOfLE hNH).symm (r, k') =
        (QuotientGroup.mk (r.out * ((k'.out : ↥H) : G)) : G ⧸ N) := by
      conv_lhs => rw [← QuotientGroup.out_eq' k']
      rfl
    rw [he, actL_eq_of_mk_eq σ ρ N hΦ]
  rw [avg_eq_sum (σ := σ) (ρ := ρ) (N := N) Φ, hsum,
    avg_eq_sum (σ := σ.comp H.subtype) (ρ := ρ.comp H.subtype) (N := N.subgroupOf H) Φ, hcard]
  simp only [actL_smul, actL_sum, Finset.smul_sum, smul_smul, Nat.cast_mul, mul_inv]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun k' _ => ?_
  congr 1
  exact actL_mul σ ρ _ _ Φ

end Tower


end TernaryPeriodPolynomials.Argument.Lemma33.Naturality
