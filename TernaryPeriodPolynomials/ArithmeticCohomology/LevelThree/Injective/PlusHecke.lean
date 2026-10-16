module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.ParityHecke

@[expose] public section


/-!
# Hecke operators commute with the parity projection `π₊`

Let `H ≤ G` be an index-two subgroup situation as in `LevelThreePeriodParityHecke`: `ε ∈ G` with
`ε² = 1` normalizing `H`, and `π₊ [z] = [(z + ι z)/2]` on `H¹(H, ρ)` where
`ι z (k) = ρ(ε) z(ε k ε)`. Let `S` be right cosets of an embedding `H → 𝔾` and `σ` a representation
of `𝔾` restricting to `ρ` on `H`.

If conjugation by `ε` extends to an involution `ε'` of `𝔾` (`Symmetry`) which fixes the set of
coset representatives of `S` (`ε' α_j ε' = α_{bar j}`), then the Hecke operator
`(T c)(k) = ∑_j σ(α_j)⁻¹ c(δ(k, j))` commutes with `ι` on cocycles
(`crossedHeckeCocycles_conjCocycle`), hence with `π₊` on `H¹` (`crossedHecke_plusMap`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.TwistSplitting
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParityHecke

namespace TernaryPeriodPolynomials.LevelThreeInjective.PlusHecke

section Generic

variable {G 𝔾 V : Type} [Group G] [Group 𝔾] [AddCommGroup V] [Module ℂ V]
  {H : Subgroup G} {ε : G} {embed : H →* 𝔾}

/-- An involution `flip` of `𝔾` extending conjugation by `ε` on `H`, together with an involution
`bar` of the coset indices with `α_{bar j} = flip α_j flip`. -/
structure Symmetry (normal : ∀ k ∈ H, ε * k * ε ∈ H) (S : RightCosets embed) where
  /-- The involution `ε'` of `𝔾`. -/
  flip : 𝔾
  flip_mul_self : flip * flip = 1
  embed_conj : ∀ k : H, embed (conjH normal k) = flip * embed k * flip
  /-- The involution on coset indices. -/
  bar : S.index → S.index
  rep_bar : ∀ j, S.rep (bar j) = flip * S.rep j * flip

namespace Symmetry

variable {normal : ∀ k ∈ H, ε * k * ε ∈ H} {S : RightCosets embed} (Y : Symmetry normal S)

theorem flip_inv : Y.flip⁻¹ = Y.flip := inv_eq_of_mul_eq_one_right Y.flip_mul_self

theorem conj_mul (a b : 𝔾) :
    Y.flip * a * Y.flip * (Y.flip * b * Y.flip) = Y.flip * (a * b) * Y.flip := by
  calc Y.flip * a * Y.flip * (Y.flip * b * Y.flip)
      = Y.flip * a * (Y.flip * Y.flip) * b * Y.flip := by group
    _ = Y.flip * (a * b) * Y.flip := by rw [Y.flip_mul_self]; group

theorem conj_inv (a : 𝔾) : (Y.flip * a * Y.flip)⁻¹ = Y.flip * a⁻¹ * Y.flip := by
  rw [mul_inv_rev, mul_inv_rev, Y.flip_inv]
  group

theorem rep_bar_bar (j : S.index) : S.rep (Y.bar (Y.bar j)) = S.rep j := by
  rw [Y.rep_bar, Y.rep_bar]
  calc Y.flip * (Y.flip * S.rep j * Y.flip) * Y.flip
      = (Y.flip * Y.flip) * S.rep j * (Y.flip * Y.flip) := by group
    _ = S.rep j := by rw [Y.flip_mul_self]; group

theorem bar_bar (j : S.index) : Y.bar (Y.bar j) = j := by
  apply S.disjoint _ _ 1
  rw [map_one, Y.rep_bar_bar, mul_inv_cancel]

/-- The involution `bar` as an equivalence of the coset indices. -/
def barEquiv : S.index ≃ S.index where
  toFun := Y.bar
  invFun := Y.bar
  left_inv := Y.bar_bar
  right_inv := Y.bar_bar

theorem rep_bar_inv (j : S.index) :
    Y.flip * (S.rep (Y.bar j))⁻¹ = (S.rep j)⁻¹ * Y.flip := by
  rw [Y.rep_bar, Y.conj_inv]
  calc Y.flip * (Y.flip * (S.rep j)⁻¹ * Y.flip)
      = (Y.flip * Y.flip) * (S.rep j)⁻¹ * Y.flip := by group
    _ = (S.rep j)⁻¹ * Y.flip := by rw [Y.flip_mul_self]; group

theorem spec_conj (k : H) (j : S.index) :
    embed (conjH normal (S.delta k j)) =
      S.rep (Y.bar j) * embed (conjH normal k) * (S.rep (Y.bar (S.next k j)))⁻¹ := by
  rw [Y.embed_conj, Y.embed_conj, S.delta_spec, Y.rep_bar, Y.rep_bar, Y.conj_inv, Y.conj_mul,
    Y.conj_mul]

theorem next_conj (k : H) (j : S.index) :
    S.next (conjH normal k) (Y.bar j) = Y.bar (S.next k j) :=
  (S.next_unique (Y.spec_conj k j)).symm

theorem delta_conj (embedded : Function.Injective embed) (k : H) (j : S.index) :
    S.delta (conjH normal k) (Y.bar j) = conjH normal (S.delta k j) :=
  (S.delta_unique embedded (by rw [Y.next_conj]; exact Y.spec_conj k j)).symm

end Symmetry

end Generic

section Hecke

variable {G 𝔾 V : Type} [Group G] [Group 𝔾] [AddCommGroup V] [Module ℂ V]
  {H : Subgroup G} {ε : G} {embed : H →* 𝔾}
  (S : RightCosets embed) (σ : Representation ℂ 𝔾 V) (ρ : Representation ℂ G V)
  (compat : ∀ k : H, (ρ.comp H.subtype) k = σ (embed k))
  (embedded : Function.Injective embed)

/-- The Hecke operator on cocycles commutes with the involution `ι`. -/
theorem crossedHeckeCocycles_conjCocycle (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (Y : Symmetry normal S) (hσ : σ Y.flip = ρ ε) (z : crossedCocycles (ρ.comp H.subtype)) :
    crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded (conjCocycle hεε normal ρ z) =
      conjCocycle hεε normal ρ (crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded z) := by
  apply Subtype.ext
  funext k
  change ∑ j, σ (S.rep j)⁻¹ (ρ ε (z.val (conjH normal (S.delta k j)))) =
    ρ ε (∑ j, σ (S.rep j)⁻¹ (z.val (S.delta (conjH normal k) j)))
  have h := Equiv.sum_comp Y.barEquiv
    (fun j => ρ ε (σ (S.rep j)⁻¹ (z.val (S.delta (conjH normal k) j))))
  rw [map_sum, ← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change σ (S.rep j)⁻¹ (ρ ε (z.val (conjH normal (S.delta k j)))) =
    ρ ε (σ (S.rep (Y.bar j))⁻¹ (z.val (S.delta (conjH normal k) (Y.bar j))))
  rw [Y.delta_conj embedded, ← hσ]
  generalize z.val (conjH normal (S.delta k j)) = w
  calc σ (S.rep j)⁻¹ (σ Y.flip w) = (σ (S.rep j)⁻¹ * σ Y.flip) w :=
        (Module.End.mul_apply _ _ _).symm
    _ = σ ((S.rep j)⁻¹ * Y.flip) w := by rw [← map_mul]
    _ = σ (Y.flip * (S.rep (Y.bar j))⁻¹) w := by rw [Y.rep_bar_inv]
    _ = (σ Y.flip * σ (S.rep (Y.bar j))⁻¹) w := by rw [map_mul]
    _ = σ Y.flip (σ (S.rep (Y.bar j))⁻¹ w) := Module.End.mul_apply _ _ _

/-- The Hecke operator on cocycles commutes with the projection `(z + ι z)/2`. -/
theorem crossedHeckeCocycles_plusLin (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (Y : Symmetry normal S) (hσ : σ Y.flip = ρ ε) (z : crossedCocycles (ρ.comp H.subtype)) :
    crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded (plusLin ρ hεε normal z) =
      plusLin ρ hεε normal (crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded z) := by
  have hc := crossedHeckeCocycles_conjCocycle S σ ρ compat embedded hεε normal Y hσ z
  change crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded
      ((2 : ℂ)⁻¹ • (z + conjCocycle hεε normal ρ z)) =
    (2 : ℂ)⁻¹ • (crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded z +
      conjCocycle hεε normal ρ (crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded z))
  rw [map_smul, map_add, hc]

/-- **The Hecke operator commutes with `π₊`.** -/
theorem crossedHecke_plusMap (hεε : ε * ε = 1) (normal : ∀ k ∈ H, ε * k * ε ∈ H)
    (Y : Symmetry normal S) (hσ : σ Y.flip = ρ ε) (x : CrossedH1 (ρ.comp H.subtype)) :
    crossedHecke S σ (ρ.comp H.subtype) compat embedded (plusMap hεε normal ρ x) =
      plusMap hεε normal ρ (crossedHecke S σ (ρ.comp H.subtype) compat embedded x) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  have hz : (crossedBoundaries (ρ.comp H.subtype)).mkQ z = Submodule.Quotient.mk z := rfl
  have hT : ∀ c : crossedCocycles (ρ.comp H.subtype),
      crossedHecke S σ (ρ.comp H.subtype) compat embedded (Submodule.Quotient.mk c) =
        Submodule.Quotient.mk
          (crossedHeckeCocycles S σ (ρ.comp H.subtype) compat embedded c) :=
    fun c => crossedHecke_mk S σ (ρ.comp H.subtype) compat embedded c
  rw [hz, plusMap_mk, hT, hT, plusMap_mk]
  exact congrArg Submodule.Quotient.mk
    (crossedHeckeCocycles_plusLin S σ ρ compat embedded hεε normal Y hσ z)

end Hecke

end TernaryPeriodPolynomials.LevelThreeInjective.PlusHecke
