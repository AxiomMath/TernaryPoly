module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FiniteIndexDescent
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturalityIso

@[expose] public section


open CategoryTheory
open scoped MatrixGroups

/-!
# Degree-one cohomology and the cuspidal condition along an isomorphism of the Levi

Formalized by Claude Sonnet 5.5.

Generalisations of `h1MapId_bijective` and `EdgeNat.mem_cuspidalFamily_map_id_iff` to a bijective homomorphism `σ : L₂ → L₁` of the groups (the Levi automorphism of `ȷ`):

* `h1Map_bijective`: a bijective `σ` and a bijective morphism `V₁ ⟶ V₂` over `σ` induce a bijection on `H¹`;
* `mem_cuspidalFamily_map_iff`: if the cusp subgroups correspond (`σ γ ∈ B₁ i ↔ γ ∈ B₂ (κ i)`, `κ` surjective), the cuspidal condition is preserved and reflected.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.SeedC3S4c

section H1

variable {L₁ L₂ : Type} [Group L₁] [Group L₂] {V₁ : Rep ℂ L₁} {V₂ : Rep ℂ L₂}
  (σ : L₂ →* L₁) (hσ : Function.Bijective σ) (φ : Rep.res σ V₁ ⟶ V₂) (hφ : Function.Bijective φ.hom)

include hσ hφ in
theorem h1Map_bijective : Function.Bijective (groupCohomology.map σ φ 1).hom := by
  let e : L₂ ≃* L₁ := MulEquiv.ofBijective σ hσ
  let T : V₁ ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective φ.hom.toLinearMap hφ
  have hT : ∀ g v, T (V₁.ρ (σ g) v) = V₂.ρ g (T v) := fun g v => Rep.hom_comm_apply φ g v
  have hmap : ∀ (c : groupCohomology.cocycles₁ V₁) (γ : L₂),
      ((groupCohomology.mapCocycles₁ σ φ c).1 γ) = φ.hom (c.1 (σ γ)) := fun c γ => rfl
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using groupCohomology.H1_induction_on with
    | h c =>
      rw [groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_eq_zero_iff] at hx
      obtain ⟨u, hu⟩ := hx
      rw [groupCohomology.H1π_eq_zero_iff]
      obtain ⟨u₁, rfl⟩ := T.surjective u
      refine ⟨u₁, ?_⟩
      funext γ'
      obtain ⟨γ, rfl⟩ := hσ.2 γ'
      have h1 := congrFun hu γ
      rw [groupCohomology.d₀₁_hom_apply] at h1 ⊢
      apply T.injective
      change T (V₁.ρ (σ γ) u₁ - u₁) = T (c.1 (σ γ))
      rw [map_sub, hT]
      exact h1.trans (hmap c γ)
  · intro x
    induction x using groupCohomology.H1_induction_on with
    | h c₂ =>
      let c₁ : groupCohomology.cocycles₁ V₁ :=
        ⟨fun γ' => T.symm (c₂.1 (e.symm γ')), by
          apply (groupCohomology.mem_cocycles₁_iff _).mpr
          intro a b
          have hrel := (groupCohomology.mem_cocycles₁_iff c₂.1).mp c₂.2 (e.symm a) (e.symm b)
          apply T.injective
          have hc : T (V₁.ρ a (T.symm (c₂.1 (e.symm b)))) = V₂.ρ (e.symm a) (c₂.1 (e.symm b)) := by
            have := hT (e.symm a) (T.symm (c₂.1 (e.symm b)))
            rw [T.apply_symm_apply] at this
            have h2 : σ (e.symm a) = a := e.apply_symm_apply a
            rw [h2] at this
            exact this
          rw [map_add, hc, T.apply_symm_apply, T.apply_symm_apply, map_mul]
          exact hrel⟩
      refine ⟨groupCohomology.H1π V₁ c₁, ?_⟩
      rw [groupCohomology.H1π_comp_map_apply]
      congr 1
      apply groupCohomology.cocycles₁_ext
      intro γ
      change T (T.symm (c₂.1 (e.symm (σ γ)))) = c₂.1 γ
      rw [T.apply_symm_apply]
      have h2 : e.symm (σ γ) = γ := e.symm_apply_apply γ
      rw [h2]

end H1

section Cusp

variable {L₁ L₂ : Type} [Group L₁] [Group L₂] {V₁ : Rep ℂ L₁} {V₂ : Rep ℂ L₂} {ι : Type}
  (σ : L₂ →* L₁) (hσ : Function.Bijective σ) (φ : Rep.res σ V₁ ⟶ V₂) (hφ : Function.Bijective φ.hom)
  (B₁ : ι → Subgroup L₁) (B₂ : ι → Subgroup L₂) (κ : ι → ι) (hκ : Function.Surjective κ)
  (hB : ∀ i γ, σ γ ∈ B₁ i ↔ γ ∈ B₂ (κ i))

include hσ hφ hκ hB in
/-- **The cuspidal condition is preserved and reflected** by a bijective morphism over a bijective `σ` carrying the cusp subgroups `B₂ (κ i)` onto `B₁ i`. -/
theorem mem_cuspidalFamily_map_iff (x : groupCohomology.H1 V₁) :
    x ∈ cuspidalFamily B₁ V₁ ↔ (groupCohomology.map σ φ 1).hom x ∈ cuspidalFamily B₂ V₂ := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [groupCohomology.H1π_comp_map_apply, mem_cuspidalFamily_π, mem_cuspidalFamily_π]
    have hmap : ∀ γ : L₂, ((groupCohomology.mapCocycles₁ σ φ c).1 γ) = φ.hom (c.1 (σ γ)) := fun γ => rfl
    constructor
    · intro H j
      obtain ⟨i, rfl⟩ := hκ j
      obtain ⟨u, hu⟩ := H i
      refine ⟨φ.hom u, fun γ => ?_⟩
      rw [hmap, hu ⟨σ γ.1, (hB i γ.1).2 γ.2⟩, map_sub]
      congr 1
      exact Rep.hom_comm_apply φ (γ : L₂) u
    · intro H i
      obtain ⟨u, hu⟩ := H (κ i)
      obtain ⟨u₁, rfl⟩ := hφ.2 u
      refine ⟨u₁, fun γ => ?_⟩
      obtain ⟨γ₂, hγ₂⟩ := hσ.2 γ.1
      have hmem : γ₂ ∈ B₂ (κ i) := (hB i γ₂).1 (by rw [hγ₂]; exact γ.2)
      apply hφ.1
      have h1 := hu ⟨γ₂, hmem⟩
      rw [hmap] at h1
      change φ.hom (c.1 (σ γ₂)) = V₂.ρ γ₂ (φ.hom u₁) - φ.hom u₁ at h1
      rw [hγ₂] at h1
      rw [h1, map_sub]
      congr 1
      have := Rep.hom_comm_apply φ γ₂ u₁
      rw [← hγ₂]
      exact this.symm

end Cusp

end TernaryPeriodPolynomials.Argument.EisensteinDual
