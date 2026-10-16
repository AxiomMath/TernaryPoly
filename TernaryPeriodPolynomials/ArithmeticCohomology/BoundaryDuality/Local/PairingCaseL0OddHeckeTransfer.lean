module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddTransport

@[expose] public section


/-!
# The transport along an involution commutes with a Hecke operator

Let `S` be a coset system `G α_j` of a group `G ⊆ 𝔾` with the Hecke operator
`(T c)(g) = ∑_j σ(α_j)⁻¹ c(α_j g α_{j g}⁻¹)` on crossed cocycles, and let `Θ c = (g ↦ E (c (a g)))`
be the transport along an endomorphism `a` of `G` and a linear map `E` with
`E (ρ (a g) v) = ρ g (E v)` (`LocalPairingCaseL0OddTransport`).  Suppose `a` extends to an
endomorphism `ã` of `𝔾`, and that `ã` permutes the cosets up to a central element `z` and elements
of `G`:

  `ã (α_j) = z · γ_j · α_{π j}`  (`π` a permutation of the cosets, `γ_j ∈ G`),

with the compatibility `σ(α_j)⁻¹ E ρ(γ_j) = E σ(α_{π j})⁻¹` of `E` at the coset representatives.
Then `T` and `Θ` commute on `H¹(G, ρ)` (`transportH1_hecke`).

The proof: `π` is compatible with the right action (`next_a`), and `ã` applied to the transition
`α_j g α_{j g}⁻¹` gives `a (δ(g, j)) = γ_j δ(a g, π j) γ_{j g}⁻¹` (`delta_a`). Expanding the cocycle
at this product, the main term of `T (Θ c)` is `Θ (T c)` by the compatibility of `E`, and the
remaining terms form the coboundary of `w = ∑_j σ(α_j)⁻¹ E c(γ_j)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddHeckeTransfer

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTransport
open TernaryPeriodPolynomials.LevelThree.GoodPlaneQuot

variable {G 𝔾 V : Type} [Group G] [Group 𝔾] [AddCommGroup V] [Module ℂ V] {embed : G →* 𝔾}

section Cosets

variable (S : RightCosets embed) (embedded : Function.Injective embed) (a : G →* G) (ã : 𝔾 →* 𝔾)
  (hã : ∀ g, ã (embed g) = embed (a g)) (z : 𝔾) (hz : ∀ x, z * x = x * z)
  (π : S.index ≃ S.index) (γ : S.index → G)
  (hA : ∀ j, ã (S.rep j) = z * embed (γ j) * S.rep (π j))

include hã hz hA in
/-- The relation `embed (γ_j⁻¹ a(δ(g, j)) γ_{j g}) = α_{π j} (a g) α_{π (j g)}⁻¹`. -/
theorem spec_a (g : G) (j : S.index) :
    embed ((γ j)⁻¹ * a (S.delta g j) * γ (S.next g j)) =
      S.rep (π j) * embed (a g) * (S.rep (π (S.next g j)))⁻¹ := by
  have h1 : embed (a (S.delta g j)) =
      ã (S.rep j) * embed (a g) * (ã (S.rep (S.next g j)))⁻¹ := by
    rw [← hã, S.delta_spec, map_mul, map_mul, map_inv, hã]
  rw [hA j, hA (S.next g j)] at h1
  have hc := hz (embed (γ j) * (S.rep (π j) * embed (a g) * (S.rep (π (S.next g j)))⁻¹) *
    (embed (γ (S.next g j)))⁻¹)
  have h2 : embed (a (S.delta g j)) = embed (γ j) * (S.rep (π j) * embed (a g) *
      (S.rep (π (S.next g j)))⁻¹) * (embed (γ (S.next g j)))⁻¹ := by
    calc embed (a (S.delta g j))
        = z * (embed (γ j) * (S.rep (π j) * embed (a g) * (S.rep (π (S.next g j)))⁻¹) *
          (embed (γ (S.next g j)))⁻¹) * z⁻¹ := by rw [h1]; group
      _ = _ := by rw [hc]; group
  simp only [map_mul, map_inv]
  rw [h2]
  group

include hã hz hA in
/-- The permutation `π` is compatible with the right action. -/
theorem next_a (g : G) (j : S.index) : S.next (a g) (π j) = π (S.next g j) :=
  (S.next_unique (spec_a S a ã hã z hz π γ hA g j)).symm

include hã hz hA embedded in
/-- The transition of the transported element. -/
theorem delta_a (g : G) (j : S.index) :
    a (S.delta g j) = γ j * S.delta (a g) (π j) * (γ (S.next g j))⁻¹ := by
  have h := S.delta_unique embedded (g := a g) (j := π j) (h := (γ j)⁻¹ * a (S.delta g j) *
    γ (S.next g j)) (by
      rw [spec_a S a ã hã z hz π γ hA g j, next_a S a ã hã z hz π γ hA g j])
  rw [← h]
  group

end Cosets

section Hecke

variable (S : RightCosets embed) (σ : Representation ℂ 𝔾 V) (ρ : Representation ℂ G V)
  (compat : ∀ g, ρ g = σ (embed g)) (embedded : Function.Injective embed) (a : G →* G)
  (ã : 𝔾 →* 𝔾) (hã : ∀ g, ã (embed g) = embed (a g)) (E : V →ₗ[ℂ] V)
  (hE : ∀ g v, E (ρ (a g) v) = ρ g (E v)) (z : 𝔾) (hz : ∀ x, z * x = x * z)
  (π : S.index ≃ S.index) (γ : S.index → G)
  (hA : ∀ j, ã (S.rep j) = z * embed (γ j) * S.rep (π j))
  (hC : ∀ j v, σ (S.rep j)⁻¹ (E (ρ (γ j) v)) = E (σ (S.rep (π j))⁻¹ v))

/-- The value of a crossed cocycle at an inverse. -/
theorem cocycle_inv (c : crossedCocycles ρ) (w : G) : c.1 w⁻¹ = -ρ w⁻¹ (c.1 w) := by
  have h := c.2 w⁻¹ w
  rw [inv_mul_cancel, crossedCocycle_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The value of a crossed cocycle at a product `x d y⁻¹`. -/
theorem cocycle_conj (c : crossedCocycles ρ) (x d y : G) :
    c.1 (x * d * y⁻¹) = c.1 x + ρ x (c.1 d) - ρ (x * d * y⁻¹) (c.1 y) := by
  rw [c.2 (x * d) y⁻¹, c.2 x d, cocycle_inv ρ c y, map_neg, ← Module.End.mul_apply, ← map_mul]
  abel

include compat embedded hã hE hz hA hC in
/-- **The difference of the two composites is a coboundary.** -/
theorem transport_hecke_sub_mem (c : crossedCocycles ρ) :
    transportCocycles ρ a E hE (crossedHeckeCocycles S σ ρ compat embedded c) -
      crossedHeckeCocycles S σ ρ compat embedded (transportCocycles ρ a E hE c) ∈
        crossedBoundaries ρ := by
  let w₀ : V := ∑ k, σ (S.rep k)⁻¹ (E (c.1 (γ k)))
  refine ⟨w₀, ?_⟩
  apply Subtype.ext
  funext g
  have hk : ∀ k, σ (S.rep k)⁻¹ (E (c.1 (a (S.delta g k)))) =
      σ (S.rep k)⁻¹ (E (c.1 (γ k))) +
        E (σ (S.rep (π k))⁻¹ (c.1 (S.delta (a g) (π k)))) -
        ρ g (σ (S.rep (S.next g k))⁻¹ (E (c.1 (γ (S.next g k))))) := by
    intro k
    have hd := delta_a S embedded a ã hã z hz π γ hA g k
    have h3 : σ (S.rep k)⁻¹ (E (ρ (a (S.delta g k)) (c.1 (γ (S.next g k))))) =
        ρ g (σ (S.rep (S.next g k))⁻¹ (E (c.1 (γ (S.next g k))))) := by
      rw [hE, compat (S.delta g k), ← Module.End.mul_apply, ← map_mul, S.rep_inv_delta, map_mul,
        Module.End.mul_apply, ← compat g]
    calc σ (S.rep k)⁻¹ (E (c.1 (a (S.delta g k))))
        = σ (S.rep k)⁻¹ (E (c.1 (γ k * S.delta (a g) (π k) * (γ (S.next g k))⁻¹))) := by
          rw [← hd]
      _ = σ (S.rep k)⁻¹ (E (c.1 (γ k) + ρ (γ k) (c.1 (S.delta (a g) (π k))) -
            ρ (γ k * S.delta (a g) (π k) * (γ (S.next g k))⁻¹) (c.1 (γ (S.next g k))))) := by
          rw [cocycle_conj ρ c]
      _ = _ := by
          rw [← hd]
          simp only [map_add, map_sub]
          rw [hC, h3]
  have hsum : ∑ k, σ (S.rep k)⁻¹ (E (c.1 (a (S.delta g k)))) =
      w₀ + E (∑ j, σ (S.rep j)⁻¹ (c.1 (S.delta (a g) j))) - ρ g w₀ := by
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      rw [map_sum]
      exact Equiv.sum_comp π (fun j => E (σ (S.rep j)⁻¹ (c.1 (S.delta (a g) j))))
    · rw [map_sum]
      exact Equiv.sum_comp (S.nextEquiv g)
        (fun j => ρ g (σ (S.rep j)⁻¹ (E (c.1 (γ j)))))
  change ρ g w₀ - w₀ = E (∑ j, σ (S.rep j)⁻¹ (c.1 (S.delta (a g) j))) -
    ∑ k, σ (S.rep k)⁻¹ (E (c.1 (a (S.delta g k))))
  rw [hsum]
  abel

include compat embedded hã hE hz hA hC in
/-- **The transport commutes with the Hecke operator on `H¹(G, ρ)`.** -/
theorem transportH1_hecke (y : CrossedH1 ρ) :
    transportH1 ρ a E hE (crossedHecke S σ ρ compat embedded y) =
      crossedHecke S σ ρ compat embedded (transportH1 ρ a E hE y) := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ y
  rw [crossedHecke_mk, show transportH1 ρ a E hE ((crossedBoundaries ρ).mkQ c) =
    (crossedBoundaries ρ).mkQ (transportCocycles ρ a E hE c) from rfl, crossedHecke_mk]
  change (crossedBoundaries ρ).mkQ
    (transportCocycles ρ a E hE (crossedHeckeCocycles S σ ρ compat embedded c)) = _
  exact (Submodule.Quotient.eq (crossedBoundaries ρ)).mpr
    (transport_hecke_sub_mem S σ ρ compat embedded a ã hã E hE z hz π γ hA hC c)

end Hecke

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddHeckeTransfer

end
