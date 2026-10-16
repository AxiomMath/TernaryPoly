module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.EdgeNaturality
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.CuspidalFamily

@[expose] public section


/-!
# Isomorphism case of the edge naturality, and bijective module morphisms

Complements `EdgeNaturality` (Lemma C.3, `ar:lem:seed`,: the face of a rational
conjugate cusp):

* `h2Map_surjective`, `h2Map_injective`: the transport of `H²` along a bijective homomorphism
  `α : E₂ → E₁` with a bijective intertwiner `T : ρ₁ → ρ₂` is bijective.
* `radH1Map_bijective`: the induced map on radical cohomology is bijective when the radical map
  `τ` and `T` are.
* `mem_cuspidalFamily_map_id_iff`: a bijective morphism `V₁ ⟶ V₂` of `L`-modules preserves and
  reflects the cuspidal condition for any family of subgroups of `L`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace EdgeNat

variable {E₁ E₂ : Type} [Group E₁] [Group E₂] (α : E₂ →* E₁)
  (ρ₁ : Rep ℂ E₁) (ρ₂ : Rep ℂ E₂) (T : ρ₁ →ₗ[ℂ] ρ₂)
  (hT : ∀ (g : E₂) (v : ρ₁), T (ρ₁.ρ (α g) v) = ρ₂.ρ g (T v))

section Surj

variable (hα : Function.Bijective α) (hTb : Function.Bijective T)

/-- The inverse cocycle of a two-cocycle along a bijective comparison. -/
def invCocycle₂ (z : groupCohomology.cocycles₂ ρ₂) : groupCohomology.cocycles₂ ρ₁ :=
  let e : E₂ ≃* E₁ := MulEquiv.ofBijective α hα
  let Te : ρ₁ ≃ₗ[ℂ] ρ₂ := LinearEquiv.ofBijective T hTb
  ⟨fun p => Te.symm (z.1 (e.symm p.1, e.symm p.2)), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h k
    have hrel := twoCocycle_relation ρ₂ z (e.symm g) (e.symm h) (e.symm k)
    have hc : ∀ (g : E₁) (w : ρ₂), ρ₁.ρ g (Te.symm w) = Te.symm (ρ₂.ρ (e.symm g) w) := by
      intro g w
      apply Te.injective
      rw [LinearEquiv.apply_symm_apply]
      have := hT (e.symm g) (Te.symm w)
      have h3 : T (Te.symm w) = w := Te.apply_symm_apply w
      rw [h3] at this
      have h2 : α (e.symm g) = g := e.apply_symm_apply g
      rw [h2] at this
      exact this
    change Te.symm (z.1 (e.symm (g * h), e.symm k)) + Te.symm (z.1 (e.symm g, e.symm h)) =
      ρ₁.ρ g (Te.symm (z.1 (e.symm h, e.symm k))) + Te.symm (z.1 (e.symm g, e.symm (h * k)))
    rw [hc, ← map_add, ← map_add, map_mul, map_mul]
    congr 1⟩

include hα hTb hT in
theorem h2Map_surjective : Function.Surjective (h2Map α ρ₁ ρ₂ T hT) := by
  intro x
  obtain ⟨z₂, rfl⟩ := twoCocycle_H2_surjective ρ₂ x
  refine ⟨groupCohomology.H2π ρ₁ (invCocycle₂ α ρ₁ ρ₂ T hT hα hTb z₂), ?_⟩
  rw [h2Map_π]
  congr 1
  apply groupCohomology.cocycles₂_ext
  intro a b
  let e : E₂ ≃* E₁ := MulEquiv.ofBijective α hα
  let Te : ρ₁ ≃ₗ[ℂ] ρ₂ := LinearEquiv.ofBijective T hTb
  change T (Te.symm (z₂.1 (e.symm (α a), e.symm (α b)))) = z₂.1 (a, b)
  have h1 : e.symm (α a) = a := e.symm_apply_apply a
  have h2 : e.symm (α b) = b := e.symm_apply_apply b
  rw [h1, h2]
  exact Te.apply_symm_apply _

include hα hTb hT in
theorem h2Map_injective : Function.Injective (h2Map α ρ₁ ρ₂ T hT) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z₁, rfl⟩ := twoCocycle_H2_surjective ρ₁ x
  rw [h2Map_π, groupCohomology.H2π_eq_zero_iff] at hx
  obtain ⟨w, hw⟩ := hx
  rw [groupCohomology.H2π_eq_zero_iff]
  let e : E₂ ≃* E₁ := MulEquiv.ofBijective α hα
  let Te : ρ₁ ≃ₗ[ℂ] ρ₂ := LinearEquiv.ofBijective T hTb
  refine ⟨fun g => Te.symm (w (e.symm g)), ?_⟩
  funext p
  have hp := congrFun hw (e.symm p.1, e.symm p.2)
  simp only [groupCohomology.d₁₂_hom_apply] at hp ⊢
  have hc : ∀ (g : E₁) (u : ρ₂), ρ₁.ρ g (Te.symm u) = Te.symm (ρ₂.ρ (e.symm g) u) := by
    intro g u
    apply Te.injective
    rw [LinearEquiv.apply_symm_apply]
    have := hT (e.symm g) (Te.symm u)
    have h3 : T (Te.symm u) = u := Te.apply_symm_apply u
    rw [h3] at this
    have h2 : α (e.symm g) = g := e.apply_symm_apply g
    rw [h2] at this
    exact this
  change ρ₁.ρ p.1 (Te.symm (w (e.symm p.2))) - Te.symm (w (e.symm (p.1 * p.2))) +
    Te.symm (w (e.symm p.1)) = z₁.1 p
  rw [hc, map_mul, ← map_sub, ← map_add]
  have hp' : ρ₂.ρ (e.symm p.1) (w (e.symm p.2)) - w (e.symm p.1 * e.symm p.2) + w (e.symm p.1) =
      T (z₁.1 (α (e.symm p.1), α (e.symm p.2))) := hp
  have h1 : α (e.symm p.1) = p.1 := e.apply_symm_apply p.1
  have h2 : α (e.symm p.2) = p.2 := e.apply_symm_apply p.2
  rw [h1, h2] at hp'
  rw [hp']
  exact Te.symm_apply_apply _


end Surj


section RadBij

variable {N₁ N₂ L₁ L₂ : Type} [Group N₁] [Group N₂] [Group L₁] [Group L₂]
  {ext₁ : GroupExtension N₁ E₁ L₁} {ext₂ : GroupExtension N₂ E₂ L₂}
  (τ : N₂ →* N₁) (hinl : ∀ r, α (ext₂.inl r) = ext₁.inl (τ r))

include hinl hT in
/-- The comparison on radical cohomology is bijective when `τ` and `T` are. -/
theorem radH1Map_bijective (hτ : Function.Bijective τ) (hTb : Function.Bijective T) :
    Function.Bijective (radH1Map α τ hinl ρ₁ ρ₂ T hT) := by
  let e : N₂ ≃* N₁ := MulEquiv.ofBijective τ hτ
  let Te : ρ₁ ≃ₗ[ℂ] ρ₂ := LinearEquiv.ofBijective T hTb
  have hc : ∀ (r : N₁) (w : ρ₂), (ρ₁.ρ (ext₁.inl r)) (Te.symm w) =
      Te.symm (ρ₂.ρ (ext₂.inl (e.symm r)) w) := by
    intro r w
    apply Te.injective
    rw [LinearEquiv.apply_symm_apply]
    have := hT_rad α τ hinl ρ₁ ρ₂ T hT (e.symm r) (Te.symm w)
    have h3 : T (Te.symm w) = w := Te.apply_symm_apply w
    rw [h3] at this
    have h2 : τ (e.symm r) = r := e.apply_symm_apply r
    rw [h2] at this
    exact this
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res ext₁.inl ρ₁) x
    rw [radH1Map_π, groupCohomology.H1π_eq_zero_iff] at hx
    obtain ⟨u, hu⟩ := hx
    rw [groupCohomology.H1π_eq_zero_iff]
    refine ⟨Te.symm u, ?_⟩
    funext r
    have := congrFun hu (e.symm r)
    simp only [groupCohomology.d₀₁_hom_apply] at this ⊢
    change ρ₁.ρ (ext₁.inl r) (Te.symm u) - Te.symm u = c.1 r
    rw [hc]
    have h2 : τ (e.symm r) = r := e.apply_symm_apply r
    have h4 : (ρ₂.ρ (ext₂.inl (e.symm r))) u - u = T (c.1 (τ (e.symm r))) := this
    rw [h2] at h4
    rw [← map_sub, h4]
    exact Te.symm_apply_apply _
  · intro x
    obtain ⟨c₂, rfl⟩ := oneCocycle_H1_surjective (Rep.res ext₂.inl ρ₂) x
    let c₁ : groupCohomology.cocycles₁ (Rep.res ext₁.inl ρ₁) :=
      ⟨fun r => Te.symm (c₂.1 (e.symm r)), by
        apply (groupCohomology.mem_cocycles₁_iff _).mpr
        intro a b
        have hrel := (groupCohomology.mem_cocycles₁_iff c₂.1).mp c₂.2 (e.symm a) (e.symm b)
        change Te.symm (c₂.1 (e.symm (a * b))) =
          ρ₁.ρ (ext₁.inl a) (Te.symm (c₂.1 (e.symm b))) + Te.symm (c₂.1 (e.symm a))
        rw [hc, ← map_add, map_mul, hrel]
        rfl⟩
    refine ⟨groupCohomology.H1π _ c₁, ?_⟩
    rw [radH1Map_π]
    congr 1
    apply groupCohomology.cocycles₁_ext
    intro r
    change T (Te.symm (c₂.1 (e.symm (τ r)))) = c₂.1 r
    have h1 : e.symm (τ r) = r := e.symm_apply_apply r
    rw [h1]
    exact Te.apply_symm_apply _

end RadBij


section CuspBij

variable {L : Type} [Group L] {ι : Type} (B : ι → Subgroup L) {V₁ V₂ : Rep ℂ L}

/-- Cuspidality is preserved and reflected by a morphism of `L`-modules that is bijective. -/
theorem mem_cuspidalFamily_map_id_iff (φ : Rep.res (MonoidHom.id L) V₁ ⟶ V₂)
    (hφ : Function.Bijective φ.hom) (x : groupCohomology.H1 V₁) :
    x ∈ cuspidalFamily B V₁ ↔
      (groupCohomology.map (MonoidHom.id L) φ 1).hom x ∈ cuspidalFamily B V₂ := by
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    rw [groupCohomology.H1π_comp_map_apply, mem_cuspidalFamily_π, mem_cuspidalFamily_π]
    refine forall_congr' fun i => ?_
    have hmap : ∀ γ : L, ((groupCohomology.mapCocycles₁ (MonoidHom.id L) φ c).1 γ) =
        φ.hom (c.1 γ) := fun γ => rfl
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨φ.hom u, fun γ => ?_⟩
      rw [hmap, hu γ, map_sub]
      congr 1
      exact Rep.hom_comm_apply φ (γ : L) u
    · rintro ⟨u, hu⟩
      obtain ⟨u₁, rfl⟩ := hφ.2 u
      refine ⟨u₁, fun γ => ?_⟩
      apply hφ.1
      rw [← hmap, hu γ, map_sub]
      congr 1
      exact (Rep.hom_comm_apply φ (γ : L) u₁).symm

end CuspBij

end EdgeNat

end TernaryPeriodPolynomials.Argument.SeedC3S4c
