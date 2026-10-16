module

public import Mathlib

@[expose] public section


/-!
# Restriction to a finite-index subgroup is injective on `H¹` (characteristic zero)

If `H ≤ G` has finite index, `ρ` is a complex representation of `G` and `φ` is a one-cocycle
(`φ (g * h) = ρ g (φ h) + φ g`) which is a coboundary on `H`, then `φ` is a coboundary on `G`.
The proof averages over the finitely many cosets of `H`.

* `exists_coboundary_of_restrict` is the elementary statement on functions.
* `H1π_eq_zero_of_restrict` and `H1π_eq_zero_of_res` are the statements in Mathlib's
  `groupCohomology` (the second one for a cocycle of the restricted representation
  `Rep.res H.subtype A`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- Summing a left-coset-invariant function over the representatives of `G ⧸ H` is invariant under
left translation. -/
theorem restrict_sum_out_reindex {G V : Type*} [Group G] [AddCommGroup V] (H : Subgroup G)
    [Fintype (G ⧸ H)] (f : G → V)
    (hf : ∀ a b : G, (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b → f a = f b) (g : G) :
    ∑ c : G ⧸ H, f (g * c.out) = ∑ c : G ⧸ H, f c.out := by
  have hinj : Function.Injective (fun c : G ⧸ H => (QuotientGroup.mk (g * c.out) : G ⧸ H)) := by
    intro c d hcd
    have h1 : (g * c.out)⁻¹ * (g * d.out) ∈ H := QuotientGroup.eq.mp hcd
    have h2 : c.out⁻¹ * d.out ∈ H := by
      have e : (g * c.out)⁻¹ * (g * d.out) = c.out⁻¹ * d.out := by group
      rwa [e] at h1
    have h3 : (QuotientGroup.mk c.out : G ⧸ H) = QuotientGroup.mk d.out :=
      QuotientGroup.eq.mpr h2
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h3
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.mp hinj) _ _ (fun c => ?_)
  exact hf _ _ (QuotientGroup.out_eq' (QuotientGroup.mk (g * c.out))).symm

/-- **Restriction to a finite-index subgroup is injective on `H¹`** (elementary form): a function
`φ : G → V` satisfying the one-cocycle identity for a complex representation `ρ`, whose restriction
to a finite-index subgroup `H` is a coboundary, is a coboundary on `G`. -/
theorem exists_coboundary_of_restrict {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) [H.FiniteIndex] (φ : G → V)
    (hφ : ∀ g h : G, φ (g * h) = ρ g (φ h) + φ g)
    (hH : ∃ v : V, ∀ h ∈ H, φ h = ρ h v - v) :
    ∃ w : V, ∀ g : G, φ g = ρ g w - w := by
  classical
  obtain ⟨v, hv⟩ := hH
  let _ : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  have : Nonempty (G ⧸ H) := ⟨QuotientGroup.mk 1⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : G → V, ∀ g, ψ g = φ g - (ρ g v - v) := ⟨_, fun _ => rfl⟩
  have hψ : ∀ g h : G, ψ (g * h) = ρ g (ψ h) + ψ g := by
    intro g h
    simp only [hψdef, hφ g h, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hψH : ∀ h ∈ H, ψ h = 0 := by
    intro h hh
    rw [hψdef, hv h hh, sub_self]
  have hcoset : ∀ a b : G, (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b → ψ a = ψ b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hψ a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hψH _ hm, map_zero, zero_add] at h1
    exact h1.symm
  obtain ⟨S, hSdef⟩ : ∃ S : V, S = ∑ c : G ⧸ H, ψ c.out := ⟨_, rfl⟩
  have hS : ∀ g : G, S = ρ g S + (Fintype.card (G ⧸ H)) • ψ g := by
    intro g
    have h1 := restrict_sum_out_reindex H ψ hcoset g
    simp only [hψ g] at h1
    rw [Finset.sum_add_distrib, ← map_sum (ρ g), Finset.sum_const, Finset.card_univ] at h1
    rw [hSdef]
    exact h1.symm
  have hcard : ((Fintype.card (G ⧸ H) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨w', hw'⟩ : ∃ w' : V, w' = (-((Fintype.card (G ⧸ H) : ℕ) : ℂ)⁻¹) • S :=
    ⟨_, rfl⟩
  refine ⟨v + w', fun g => ?_⟩
  have h2 : ρ g S - S = -(((Fintype.card (G ⧸ H) : ℕ) : ℂ) • ψ g) := by
    rw [Nat.cast_smul_eq_nsmul ℂ]
    linear_combination (norm := abel) -(hS g)
  have key : ρ g w' - w' = ψ g := by
    rw [hw', map_smul, ← smul_sub, h2, smul_neg, neg_smul, neg_neg, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
  have hφg : φ g = ψ g + (ρ g v - v) := by
    rw [hψdef]
    abel
  calc φ g = (ρ g w' - w') + (ρ g v - v) := by rw [key]; exact hφg
    _ = ρ g (v + w') - (v + w') := by rw [map_add]; abel

/-- **Restriction to a finite-index subgroup is injective on `H¹`** (Mathlib's group cohomology): a
one-cocycle `φ` of `A` whose values on a finite-index subgroup `H` are those of the coboundary of
a vector `v` has zero class. -/
theorem H1π_eq_zero_of_restrict {G : Type} [Group G] (A : Rep ℂ G) (H : Subgroup G)
    [H.FiniteIndex] (φ : groupCohomology.cocycles₁ A) (v : A)
    (hv : ∀ h ∈ H, φ h = A.ρ h v - v) :
    groupCohomology.H1π A φ = 0 := by
  rw [groupCohomology.H1π_eq_zero_iff]
  have hcoc : ∀ g h : G, φ (g * h) = A.ρ g (φ h) + φ g :=
    fun g h => (groupCohomology.mem_cocycles₁_iff φ).mp φ.property g h
  obtain ⟨w, hw⟩ := exists_coboundary_of_restrict A.ρ H (fun g => φ g) hcoc ⟨v, hv⟩
  refine ⟨w, ?_⟩
  funext g
  change A.ρ g w - w = φ g
  exact (hw g).symm

/-- **Restriction to a finite-index subgroup is injective on `H¹`**, stated with the restricted
representation `Rep.res H.subtype A`: if the cocycle `ψ` of the restriction, which agrees with `φ`
on `H`, has zero class, then so does `φ`. -/
theorem H1π_eq_zero_of_res {G : Type} [Group G] (A : Rep ℂ G) (H : Subgroup G)
    [H.FiniteIndex] (φ : groupCohomology.cocycles₁ A)
    (ψ : groupCohomology.cocycles₁ (Rep.res H.subtype A))
    (hψ : ∀ h : H, ψ h = φ h.1)
    (hzero : groupCohomology.H1π (Rep.res H.subtype A) ψ = 0) :
    groupCohomology.H1π A φ = 0 := by
  obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff ψ).mp hzero
  refine H1π_eq_zero_of_restrict A H φ (v : A) ?_
  intro h hh
  have e : (Rep.res H.subtype A).ρ ⟨h, hh⟩ v - v = ψ ⟨h, hh⟩ := congrFun hv ⟨h, hh⟩
  exact (hψ ⟨h, hh⟩).symm.trans e.symm

end TernaryPeriodPolynomials.SourceConstruction
