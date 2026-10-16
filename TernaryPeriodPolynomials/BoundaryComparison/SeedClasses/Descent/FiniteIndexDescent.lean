module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.MixedCuspidal

@[expose] public section


/-!
# Finite-index descent of the cuspidal condition (the Levi `L_P` versus `Γ₂(N)`)

Paper: Lemma C.3 (`ar:lem:seed`),
 ("The radical is a lattice in `ℝ²`, and the Levi has a finite-index subgroup acting on
a modular curve") and ("The finite reflection projection supplies the corresponding
full-level statement").

The arithmetic Levi quotient `L_P` of a plane group is only a finite extension of the group `Γ₂(N)`
acting on a modular curve (reflections, congruence quotient). The mixed cuspidal condition for `L_P`
reduces to the same condition for the finite-index subgroup `Λ`:

* `coboundary_of_finiteIndex`: a 1-cocycle of a group `H` with values in a `ℂ`-module which is a
  coboundary on a finite-index subgroup `K` is a coboundary (averaging over the cosets `H/K`).
* `mem_cuspidalFamily_iff_res`: for `Λ ≤ L` of finite index, a class `x ∈ H¹(L, V)` vanishes on every
  cusp subgroup `B i ≤ L` iff its restriction `x|_Λ ∈ H¹(Λ, V)` vanishes on every `B i ∩ Λ`
  (`oneRestriction Λ V`). With cusp subgroups indexed by rational frames, this is: `x` is mixed
  cuspidal for the finite extension `L` iff `x|_Λ` is mixed cuspidal for `Λ`
  (`cuspidalFamily_eq_comap`).

Together with the degree-two level transfer `H²(S) ≃ H²(N)^{S/N}` (`Statements.LevelTransfer`) this is
the cohomological input of the finite reflection projection; the reflection group and the seeds
`SeedC3S4c.reflSeedInv` have not been assembled with it here.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped BigOperators MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

/-- A cocycle which is a coboundary on a finite-index subgroup is a coboundary. -/
theorem coboundary_of_finiteIndex {H : Type} [Group H] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (K : Subgroup H) [Finite (H ⧸ K)]
    (c : H → V) (hc : ∀ x y, c (x * y) = ρ x (c y) + c x) (u : V)
    (hu : ∀ k ∈ K, c k = ρ k u - u) : ∃ v : V, ∀ h : H, c h = ρ h v - v := by
  classical
  have : Fintype (H ⧸ K) := Fintype.ofFinite _
  set ct : H → V := fun x => c x - (ρ x u - u) with hct
  have hct_mul : ∀ x y, ct (x * y) = ρ x (ct y) + ct x := by
    intro x y
    simp only [hct, hc, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hct_K : ∀ k ∈ K, ct k = 0 := by
    intro k hk
    simp only [hct, hu k hk, sub_self]
  have hct_coset : ∀ x, ∀ k ∈ K, ct (x * k) = ct x := by
    intro x k hk
    rw [hct_mul, hct_K k hk, map_zero, zero_add]
  set m : ℕ := Fintype.card (H ⧸ K) with hm
  have hmpos : (m : ℂ) ≠ 0 := by
    have : 0 < m := Fintype.card_pos
    exact_mod_cast this.ne'
  set S : V := ∑ q : H ⧸ K, ct q.out with hS
  have key : ∀ h : H, S = (m : ℂ) • ct h + ρ h S := by
    intro h
    have h1 : ∑ q : H ⧸ K, ct (h * q.out) = S := by
      have hterm : ∀ q : H ⧸ K, ct (h * q.out) = ct ((h • q).out) := by
        intro q
        have hq : (QuotientGroup.mk (h * q.out) : H ⧸ K) = h • q := by
          conv_rhs => rw [← QuotientGroup.out_eq' q]
          rfl
        have hq2 : (QuotientGroup.mk ((h • q).out) : H ⧸ K) = h • q := QuotientGroup.out_eq' _
        have hk : ((h • q).out)⁻¹ * (h * q.out) ∈ K := QuotientGroup.eq.mp (hq2.trans hq.symm)
        have : h * q.out = (h • q).out * (((h • q).out)⁻¹ * (h * q.out)) := by group
        rw [this, hct_coset _ _ hk]
      rw [Finset.sum_congr rfl (fun q _ => hterm q)]
      exact Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (H ⧸ K)) (fun q => ct q.out)
    have h2 : ∑ q : H ⧸ K, ct (h * q.out) = (m : ℂ) • ct h + ρ h S := by
      simp only [hct_mul, Finset.sum_add_distrib, ← map_sum, Finset.sum_const, Finset.card_univ, hm,
        hS]
      rw [add_comm, ← Nat.cast_smul_eq_nsmul ℂ]
    exact h1.symm.trans h2
  refine ⟨u - (m : ℂ)⁻¹ • S, fun h => ?_⟩
  have hk := key h
  have hcth : c h = ct h + (ρ h u - u) := by simp [hct]
  have h4 : S - ρ h S = (m : ℂ) • ct h := by linear_combination (norm := module) hk
  have h3 : ct h = (m : ℂ)⁻¹ • (S - ρ h S) := by
    rw [h4, smul_smul, inv_mul_cancel₀ hmpos, one_smul]
  rw [hcth, h3, map_sub, map_smul]
  module

section Descent

variable {L : Type} [Group L]

/-- The cuspidal subspace of `H¹(L, V)` attached to an arbitrary family of cusp subgroups `B i`. -/
def cuspidalFamily {ι : Type} (B : ι → Subgroup L) (V : Rep ℂ L) :
    Submodule ℂ (groupCohomology.H1 V) :=
  ⨅ i, LinearMap.ker (oneRestriction (B i) V)

theorem cuspidalSubspace_eq_family (Λ : Subgroup SL(2, ℤ)) (V : Rep ℂ Λ) :
    cuspidalSubspace Λ V = cuspidalFamily (leviCuspStab Λ) V := rfl

theorem mem_cuspidalFamily_π {ι : Type} (B : ι → Subgroup L) (V : Rep ℂ L)
    (c : groupCohomology.cocycles₁ V) :
    groupCohomology.H1π V c ∈ cuspidalFamily B V ↔
      ∀ i, ∃ u : V, ∀ γ : B i, c.1 (γ : L) = V.ρ (γ : L) u - u := by
  unfold cuspidalFamily
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact forall_congr' fun i => oneRestriction_π_eq_zero_iff _ V c

/-- **Finite-index descent of the cuspidal condition.** For a subgroup `Λ ≤ L` of finite index, a
class `x ∈ H¹(L, V)` vanishes on every cusp subgroup `B i` iff its restriction to `Λ` vanishes on
every `B i ∩ Λ`. -/
theorem mem_cuspidalFamily_iff_res {ι : Type} (B : ι → Subgroup L) (V : Rep ℂ L)
    (Λ : Subgroup L) [Λ.FiniteIndex] (x : groupCohomology.H1 V) :
    x ∈ cuspidalFamily B V ↔
      oneRestriction Λ V x ∈ cuspidalFamily (fun i => (B i).comap Λ.subtype)
        (Rep.res Λ.subtype V) := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [oneRestriction_π, mem_cuspidalFamily_π, mem_cuspidalFamily_π]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, fun γ => hu ⟨(γ : Λ).1, γ.2⟩⟩
    · rintro ⟨u, hu⟩
      have hfin : Finite (↥(B i) ⧸ Λ.subgroupOf (B i)) := inferInstance
      obtain ⟨v, hv⟩ := coboundary_of_finiteIndex (H := ↥(B i)) (V := V)
        (V.ρ.comp (B i).subtype) (Λ.subgroupOf (B i)) (fun h => c.1 (h : L))
        (fun x y => (groupCohomology.mem_cocycles₁_iff c.1).mp c.2 (x : L) (y : L)) u
        (fun k hk => hu ⟨⟨(k : L), Subgroup.mem_subgroupOf.mp hk⟩, k.2⟩)
      exact ⟨v, fun γ => hv γ⟩

/-- The cuspidal subspace of `H¹(L, V)` is the preimage of the cuspidal subspace of the
finite-index subgroup `Λ` under restriction. -/
theorem cuspidalFamily_eq_comap {ι : Type} (B : ι → Subgroup L) (V : Rep ℂ L)
    (Λ : Subgroup L) [Λ.FiniteIndex] :
    cuspidalFamily B V = Submodule.comap (oneRestriction Λ V)
      (cuspidalFamily (fun i => (B i).comap Λ.subtype) (Rep.res Λ.subtype V)) := by
  ext x
  exact mem_cuspidalFamily_iff_res B V Λ x

end Descent

end TernaryPeriodPolynomials.Argument.SeedC3S4c
