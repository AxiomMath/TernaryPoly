module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1

@[expose] public section


/-!
# The transport of crossed homomorphisms intertwines Hecke operators (abstract form)

Let `ι : G → 𝔾` be an embedding with right coset data `S` (`HeckeH1.RightCosets`), `σ₁`, `σ₂`
representations of `𝔾` on `V₁`, `V₂` restricting to `ρ₁`, `ρ₂` on `G`, `a : G → G` multiplicative
and
`ã : 𝔾 → 𝔾` a homomorphism with `ι ∘ a = ã ∘ ι`, and `E : V₁ → V₂` linear with
`E ρ₁(a g) = ρ₂(g) E`.  Suppose `ã` permutes the right cosets up to a central element `z`:
`ã(α_j) = z · ι(u_j) · α_{τ j}` for a bijection `τ` and elements `u_j ∈ G`, and that
`E σ₁(ι(u_j) α_{τ j}) = κ σ₂(α_j) E`.  Then the Hecke operators
`T_i c (g) = ∑_j σ_i(α_j)⁻¹ c(δ(g, j))`
satisfy, on the transport `Θ y (g) = - E y(a g)`,

  `T₂ (Θ y) = κ Θ (T₁ y) + (coboundary)`,

so `T₂ ∘ Θ = κ Θ ∘ T₁` on `H¹`.  The coboundary is that of `∑_k σ₂(α_k)⁻¹ E y(u_k)`: changing the
coset
representatives `α_{τ j}` by `u_j` changes a Hecke cocycle by a coboundary.

The coset transitions are handled with the uniqueness statements `RightCosets.next_unique` and
`RightCosets.delta_unique`: the identity
`ι(a δ(g, j)) = ι(u_j) · α_{τ j} ι(a g) α_{τ j'}⁻¹ · ι(u_{j'})⁻¹` (`j' = next g j`) shows
`a δ(g, j) = u_j · δ(a g, τ j) · u_{j'}⁻¹` and `τ j' = next (a g) (τ j)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

/-- The value of a crossed homomorphism at `a b c⁻¹`. -/
theorem crossed_apply_mul_mul_inv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (y : crossedCocycles ρ) (a b c : G) :
    y.1 (a * b * c⁻¹) = y.1 a + ρ a (y.1 b) - ρ (a * b * c⁻¹) (y.1 c) := by
  have h1 := y.2 (a * b * c⁻¹) c
  rw [inv_mul_cancel_right, y.2 a b] at h1
  exact eq_sub_of_add_eq h1.symm

section Abstract

variable {G 𝔾 V₁ V₂ : Type} [Group G] [Group 𝔾] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {ι : G →* 𝔾}

/-- **The transition of the coset data under the automorphism pair.**  If
`ã(α_j) = z ι(u_j) α_{τ j}`
with `z` central, then `a δ(g, j) = u_j δ(a g, τ j) u_{next g j}⁻¹` and
`τ (next g j) = next (a g) (τ j)`. -/
theorem delta_transition (S : RightCosets ι) (hι : Function.Injective ι) (a : G → G)
    (ã : 𝔾 →* 𝔾) (haι : ∀ g, ι (a g) = ã (ι g)) (z : 𝔾) (hz : ∀ x, z * x = x * z)
    (τ : S.index → S.index) (u : S.index → G)
    (hτ : ∀ j, ã (S.rep j) = z * (ι (u j) * S.rep (τ j))) (g : G) (j : S.index) :
    τ (S.next g j) = S.next (a g) (τ j) ∧
      a (S.delta g j) = u j * S.delta (a g) (τ j) * (u (S.next g j))⁻¹ := by
  have hzc : ∀ x, z * x * z⁻¹ = x := fun x => by rw [hz x, mul_inv_cancel_right]
  have key : ι (a (S.delta g j)) = ι (u j) * (S.rep (τ j) * ι (a g) * (S.rep (τ (S.next g j)))⁻¹) *
      (ι (u (S.next g j)))⁻¹ := by
    rw [haι, S.delta_spec, map_mul, map_mul, map_inv, hτ j, hτ (S.next g j), ← haι]
    have e : z * (ι (u j) * S.rep (τ j)) * ι (a g) *
        (z * (ι (u (S.next g j)) * S.rep (τ (S.next g j))))⁻¹ =
        z * (ι (u j) * (S.rep (τ j) * ι (a g) * (S.rep (τ (S.next g j)))⁻¹) *
          (ι (u (S.next g j)))⁻¹) * z⁻¹ := by
      group
    rw [e, hzc]
  set h : G := (u j)⁻¹ * a (S.delta g j) * u (S.next g j) with hh
  have hspec : ι h = S.rep (τ j) * ι (a g) * (S.rep (τ (S.next g j)))⁻¹ := by
    rw [hh, map_mul, map_mul, map_inv, key]
    group
  have hnext : τ (S.next g j) = S.next (a g) (τ j) := S.next_unique hspec
  refine ⟨hnext, ?_⟩
  have hdelta : h = S.delta (a g) (τ j) := by
    apply S.delta_unique hι
    rw [← hnext]
    exact hspec
  rw [← hdelta, hh]
  group

variable (S : RightCosets ι) (hι : Function.Injective ι)
  (σ₁ : Representation ℂ 𝔾 V₁) (σ₂ : Representation ℂ 𝔾 V₂)
  (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
  (c₁ : ∀ g, ρ₁ g = σ₁ (ι g)) (c₂ : ∀ g, ρ₂ g = σ₂ (ι g))
  (a : G → G) (ha : ∀ g h, a (g * h) = a g * a h) (E : V₁ →ₗ[ℂ] V₂)
  (hE : ∀ g v, E (ρ₁ (a g) v) = ρ₂ g (E v))

include hι c₁ c₂ in
/-- **Hecke operators and the transport (cocycle level).** -/
theorem hecke_transportCocycles_apply (ã : 𝔾 →* 𝔾) (haι : ∀ g, ι (a g) = ã (ι g)) (z : 𝔾)
    (hz : ∀ x, z * x = x * z) (τ : S.index ≃ S.index) (u : S.index → G)
    (hτ : ∀ j, ã (S.rep j) = z * (ι (u j) * S.rep (τ j))) (κ : ℂ)
    (hEr : ∀ j v, E (σ₁ (ι (u j) * S.rep (τ j)) v) = κ • σ₂ (S.rep j) (E v))
    (y : crossedCocycles ρ₁) (g : G) :
    (crossedHeckeCocycles S σ₂ ρ₂ c₂ hι (transportCocycles ρ₁ ρ₂ a ha E hE y)).val g =
      κ • (transportCocycles ρ₁ ρ₂ a ha E hE (crossedHeckeCocycles S σ₁ ρ₁ c₁ hι y)).val g +
        (crossedBoundary ρ₂ (∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k))))).val g := by
  have step : ∀ j, σ₂ (S.rep j)⁻¹ ((transportCocycles ρ₁ ρ₂ a ha E hE y).val (S.delta g j)) =
      -(σ₂ (S.rep j)⁻¹ (E (y.val (u j)))) -
        κ • E (σ₁ (S.rep (τ j))⁻¹ (y.val (S.delta (a g) (τ j)))) +
        ρ₂ g (σ₂ (S.rep (S.next g j))⁻¹ (E (y.val (u (S.next g j))))) := by
    intro j
    obtain ⟨hnext, hdelta⟩ := delta_transition S hι a ã haι z hz τ u hτ g j
    have hcoc := crossed_apply_mul_mul_inv ρ₁ y (u j) (S.delta (a g) (τ j)) (u (S.next g j))
    rw [← hdelta] at hcoc
    have h3 : ∀ v, σ₂ (S.rep j)⁻¹ (E (ρ₁ (u j) v)) = κ • E (σ₁ (S.rep (τ j))⁻¹ v) := by
      intro v
      have h := hEr j (σ₁ (S.rep (τ j))⁻¹ v)
      have e1 : σ₁ (ι (u j) * S.rep (τ j)) (σ₁ (S.rep (τ j))⁻¹ v) = ρ₁ (u j) v := by
        rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (σ₁ (S.rep (τ j))),
          ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, c₁]
      rw [e1] at h
      rw [h, map_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have h4 : σ₂ (S.rep j)⁻¹ (ρ₂ (S.delta g j) (E (y.val (u (S.next g j))))) =
        ρ₂ g (σ₂ (S.rep (S.next g j))⁻¹ (E (y.val (u (S.next g j))))) := by
      have := S.rep_inv_delta g j
      rw [c₂, c₂, ← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]
    change σ₂ (S.rep j)⁻¹ (-E (y.val (a (S.delta g j)))) = _
    rw [hcoc]
    simp only [map_sub, map_add, neg_sub]
    rw [hE, h4, h3]
    abel
  have e1 : ∑ j, κ • E (σ₁ (S.rep (τ j))⁻¹ (y.val (S.delta (a g) (τ j)))) =
      κ • ∑ k, E (σ₁ (S.rep k)⁻¹ (y.val (S.delta (a g) k))) := by
    rw [← Finset.smul_sum]
    congr 1
    exact Equiv.sum_comp τ (fun k => E (σ₁ (S.rep k)⁻¹ (y.val (S.delta (a g) k))))
  have e2 : ∑ j, ρ₂ g (σ₂ (S.rep (S.next g j))⁻¹ (E (y.val (u (S.next g j))))) =
      ρ₂ g (∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k)))) := by
    rw [map_sum]
    exact Equiv.sum_comp (S.nextEquiv g) (fun k => ρ₂ g (σ₂ (S.rep k)⁻¹ (E (y.val (u k)))))
  have hsum : ∑ j, σ₂ (S.rep j)⁻¹ ((transportCocycles ρ₁ ρ₂ a ha E hE y).val (S.delta g j)) =
      -(∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k)))) -
        κ • ∑ k, E (σ₁ (S.rep k)⁻¹ (y.val (S.delta (a g) k))) +
        ρ₂ g (∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k)))) := by
    rw [Finset.sum_congr rfl (fun j _ => step j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, e1, e2]
  change ∑ j, σ₂ (S.rep j)⁻¹ ((transportCocycles ρ₁ ρ₂ a ha E hE y).val (S.delta g j)) =
    κ • (-E (∑ k, σ₁ (S.rep k)⁻¹ (y.val (S.delta (a g) k)))) +
      (ρ₂ g (∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k)))) - ∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k))))
  rw [hsum, map_sum E, smul_neg]
  abel

/-- **`τ` is injective** when `ã` is an involution: if `τ j = τ j'` then `ã(α_j α_{j'}⁻¹) ∈ ι(G)`,
so `α_j α_{j'}⁻¹ = ã ã (α_j α_{j'}⁻¹) ∈ ι(G)` and the cosets agree. -/
theorem tau_injective (S : RightCosets ι) (a : G → G) (ã : 𝔾 →* 𝔾)
    (haι : ∀ g, ι (a g) = ã (ι g)) (hãã : ∀ x, ã (ã x) = x) (z : 𝔾) (hz : ∀ x, z * x = x * z)
    (τ : S.index → S.index) (u : S.index → G)
    (hτ : ∀ j, ã (S.rep j) = z * (ι (u j) * S.rep (τ j))) : Function.Injective τ := by
  intro j j' hjj
  have hzc : ∀ x, z * x * z⁻¹ = x := fun x => by rw [hz x, mul_inv_cancel_right]
  have h1 : ã (S.rep j * (S.rep j')⁻¹) = ι (u j * (u j')⁻¹) := by
    rw [map_mul, map_inv, hτ j, hτ j', hjj, map_mul, map_inv]
    have e : z * (ι (u j') * S.rep (τ j'))
        = z * (ι (u j') * S.rep (τ j')) := rfl
    have e2 : z * (ι (u j) * S.rep (τ j')) * (z * (ι (u j') * S.rep (τ j')))⁻¹ =
        z * (ι (u j) * (ι (u j'))⁻¹) * z⁻¹ := by
      group
    rw [e2, hzc]
  have h2 : ι (a (u j * (u j')⁻¹)) = S.rep j * (S.rep j')⁻¹ := by
    rw [haι, ← h1, hãã]
  exact S.disjoint j j' _ h2

/-- **The transport intertwines the Hecke operators on `H¹`**: `T₂ ∘ Θ = κ · Θ ∘ T₁`. -/
theorem hecke_transportH1 (ã : 𝔾 →* 𝔾) (haι : ∀ g, ι (a g) = ã (ι g))
    (hãã : ∀ x, ã (ã x) = x) (z : 𝔾) (hz : ∀ x, z * x = x * z) (τ : S.index → S.index)
    (u : S.index → G) (hτ : ∀ j, ã (S.rep j) = z * (ι (u j) * S.rep (τ j))) (κ : ℂ)
    (hEr : ∀ j v, E (σ₁ (ι (u j) * S.rep (τ j)) v) = κ • σ₂ (S.rep j) (E v))
    (x : CrossedH1 ρ₁) :
    crossedHecke S σ₂ ρ₂ c₂ hι (transportH1 ρ₁ ρ₂ a ha E hE x) =
      κ • transportH1 ρ₁ ρ₂ a ha E hE (crossedHecke S σ₁ ρ₁ c₁ hι x) := by
  have hinj := tau_injective S a ã haι hãã z hz τ u hτ
  let τe : S.index ≃ S.index := Equiv.ofBijective τ ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [transportH1_mk, crossedHecke_mk, crossedHecke_mk, transportH1_mk, ← map_smul]
  have hcoc : crossedHeckeCocycles S σ₂ ρ₂ c₂ hι (transportCocycles ρ₁ ρ₂ a ha E hE y) =
      κ • transportCocycles ρ₁ ρ₂ a ha E hE (crossedHeckeCocycles S σ₁ ρ₁ c₁ hι y) +
        crossedBoundary ρ₂ (∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k)))) := by
    apply Subtype.ext
    funext g
    exact hecke_transportCocycles_apply S hι σ₁ σ₂ ρ₁ ρ₂ c₁ c₂ a ha E hE ã haι z hz τe u hτ κ hEr
      y g
  rw [hcoc, map_add, map_smul]
  have h0 : (crossedBoundaries ρ₂).mkQ
      (crossedBoundary ρ₂ (∑ k, σ₂ (S.rep k)⁻¹ (E (y.val (u k))))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [h0, add_zero]


end Abstract

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
