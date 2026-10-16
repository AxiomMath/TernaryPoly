module

public import Mathlib

@[expose] public section


/-!
# A coset-sum identity for a free action of a finite-index normal subgroup

Formalized by Claude Sonnet 5.5.

For `N ⊲ K` of finite index, `T₀` with trivial stabilizer in `N`, the sum over `K/N` of `Φ(g s)` over those cosets `s` for which some
`g ∈ N` has `g s T = T₀` equals the sum of `Φ` over a finite set `S = {h | h T = T₀}`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open scoped Classical

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {K X B : Type*} [Group K] [MulAction K X] [AddCommMonoid B] (N : Subgroup K) [N.Normal]
  [N.FiniteIndex]

/-- The element `g s` for the coset `s`, when it exists. -/
def cosetElt (T T₀ : X) (s : K ⧸ N) : K :=
  if hh : ∃ g ∈ N, g • ((s.out : K) • T) = T₀ then hh.choose * s.out else 1

omit [N.FiniteIndex] in
theorem coset_exists_iff (T T₀ : X) (hfree : ∀ g ∈ N, g • T₀ = T₀ → g = 1) (h : K) :
    h • T = T₀ ↔ ∃ s : K ⧸ N, (∃ g ∈ N, g • ((s.out : K) • T) = T₀) ∧ cosetElt N T T₀ s = h := by
  constructor
  · intro hT
    set s : K ⧸ N := (h : K ⧸ N) with hsdef
    have hs : (((s.out : K) : K ⧸ N)) = s := QuotientGroup.out_eq' _
    have hn : h⁻¹ * s.out ∈ N := QuotientGroup.eq.mp (by rw [hs])
    have hg : h * (s.out)⁻¹ ∈ N := by
      have := Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hn) h
      simpa [mul_assoc] using this
    have hex : ∃ g ∈ N, g • ((s.out : K) • T) = T₀ :=
      ⟨h * (s.out)⁻¹, hg, by rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one, hT]⟩
    refine ⟨s, hex, ?_⟩
    unfold cosetElt
    rw [dite_eq_left hex]
    obtain ⟨hg', hg'T⟩ := hex.choose_spec
    set g' := hex.choose
    have hk : g' * s.out * h⁻¹ ∈ N := by
      have : g' * s.out * h⁻¹ = g' * (h * (h⁻¹ * s.out) * h⁻¹) := by group
      rw [this]
      exact N.mul_mem hg' (Subgroup.Normal.conj_mem inferInstance _ hn h)
    have hk1 : g' * s.out * h⁻¹ = 1 := by
      apply hfree _ hk
      rw [← hT, ← mul_smul, show g' * s.out * h⁻¹ * h = g' * s.out by group, mul_smul, hg'T, hT]
    exact (mul_inv_eq_one.mp hk1)
  · rintro ⟨s, hs, rfl⟩
    unfold cosetElt
    rw [dite_eq_left hs]
    obtain ⟨hg', hg'T⟩ := hs.choose_spec
    rw [mul_smul]
    exact hg'T

omit [N.FiniteIndex] in
theorem cosetElt_mk (T T₀ : X) (s : K ⧸ N) (hs : ∃ g ∈ N, g • ((s.out : K) • T) = T₀) :
    ((cosetElt N T T₀ s : K) : K ⧸ N) = s := by
  unfold cosetElt
  rw [dite_eq_left hs]
  obtain ⟨hg', -⟩ := hs.choose_spec
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff hs.choose).mpr hg', one_mul]
  exact QuotientGroup.out_eq' s

theorem coset_sum_eq (T T₀ : X) (hfree : ∀ g ∈ N, g • T₀ = T₀ → g = 1) (Φ : K → B) (S : Finset K)
    (hS : ∀ h, h ∈ S ↔ h • T = T₀) :
    ∑ s : K ⧸ N, (if (∃ g ∈ N, g • ((s.out : K) • T) = T₀) then Φ (cosetElt N T T₀ s) else 0) =
      ∑ h ∈ S, Φ h := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun s _ => cosetElt N T T₀ s) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact (hS _).mpr ((coset_exists_iff N T T₀ hfree _).mpr ⟨s, hs.2, rfl⟩)
  · intro s hs s' hs' h
    rw [Finset.mem_filter] at hs hs'
    rw [← cosetElt_mk N T T₀ s hs.2, ← cosetElt_mk N T T₀ s' hs'.2, h]
  · intro h hh
    obtain ⟨s, hs, hsh⟩ := (coset_exists_iff N T T₀ hfree h).mp ((hS h).mp hh)
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, hsh⟩

end TernaryPeriodPolynomials.Argument.GroupHomology
