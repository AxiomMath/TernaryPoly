module

public import TernaryPeriodPolynomials.Topology.TopHomology.PermutationHom

@[expose] public section


/-!
# Equivariant lifting with carriers

For a free `Γ`-set `S`, a morphism of representations `φ : Y ⟶ Z`, subspaces `KY s ⊆ Y` that are permuted by `Γ`
along the action on `S`, and an equivariant function `z : S → Z` with `z s ∈ φ(KY s)`, there is an equivariant
`y : S → Y` with `y s ∈ KY s` and `φ (y s) = z s` (`exists_equivariant_lift`).  This is the single non-formal
step of the equivariant acyclic-carrier arguments of `CapCompat`: choose a preimage on orbit representatives and
translate.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

theorem exists_equivariant_lift {S : Type} [MulAction Γ S] (hfree : ∀ (γ : Γ) (s : S), γ • s = s → γ = 1)
    {Y Z : Rep.{0} ℚ Γ} (φ : Y ⟶ Z) (KY : S → Submodule ℚ Y)
    (hKY : ∀ (γ : Γ) (s : S), KY (γ • s) = (KY s).map (Y.ρ γ))
    (z : S → Z) (hz : ∀ (γ : Γ) (s : S), z (γ • s) = Z.ρ γ (z s))
    (hzK : ∀ s, z s ∈ (KY s).map φ.hom.toLinearMap) :
    ∃ y : S → Y, (∀ (γ : Γ) (s : S), y (γ • s) = Y.ρ γ (y s)) ∧ (∀ s, y s ∈ KY s) ∧
      ∀ s, φ.hom (y s) = z s := by
  classical
  let s0 : S → S := fun y => Quotient.out (Quotient.mk (MulAction.orbitRel Γ S) y)
  have hs : ∀ y, ∃ γ : Γ, γ • s0 y = y := fun y => by
    have h : (MulAction.orbitRel Γ S) y (s0 y) :=
      (MulAction.orbitRel Γ S).symm (Quotient.mk_out (s := MulAction.orbitRel Γ S) y)
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp h
    exact ⟨γ, hγ⟩
  let g : S → Γ := fun y => Classical.choose (hs y)
  have hg : ∀ y, g y • s0 y = y := fun y => Classical.choose_spec (hs y)
  have hs_eq : ∀ (γ : Γ) (y : S), s0 (γ • y) = s0 y := fun γ y => by
    have : Quotient.mk (MulAction.orbitRel Γ S) (γ • y) = Quotient.mk (MulAction.orbitRel Γ S) y :=
      Quotient.sound (MulAction.orbitRel_apply.mpr ⟨γ, rfl⟩)
    simp only [s0, this]
  have hg_eq : ∀ (γ : Γ) (y : S), g (γ • y) = γ * g y := fun γ y => by
    have h1 : g (γ • y) • s0 y = γ • y := by
      have := hg (γ • y)
      rwa [hs_eq] at this
    have h2 : (γ * g y) • s0 y = γ • y := by rw [mul_smul, hg]
    have h3 : ((γ * g y)⁻¹ * g (γ • y)) • s0 y = s0 y := by
      rw [mul_smul, h1, ← h2, inv_smul_smul]
    have := hfree _ _ h3
    calc g (γ • y) = (γ * g y) * ((γ * g y)⁻¹ * g (γ • y)) := (mul_inv_cancel_left _ _).symm
      _ = γ * g y := by rw [this, mul_one]
  have hex : ∀ y, ∃ a : Y, a ∈ KY y ∧ φ.hom a = z y := fun y => by
    obtain ⟨a, ha, hφ⟩ := hzK y
    exact ⟨a, ha, hφ⟩
  let a' : S → Y := fun y => Classical.choose (hex y)
  have ha'K : ∀ y, a' y ∈ KY y := fun y => (Classical.choose_spec (hex y)).1
  have ha'φ : ∀ y, φ.hom (a' y) = z y := fun y => (Classical.choose_spec (hex y)).2
  refine ⟨fun y => Y.ρ (g y) (a' (s0 y)), fun γ y => ?_, fun y => ?_, fun y => ?_⟩
  · simp only [hg_eq, hs_eq, map_mul, Module.End.mul_apply]
  · have : KY y = KY (g y • s0 y) := by rw [hg]
    rw [this, hKY]
    exact ⟨a' (s0 y), ha'K _, rfl⟩
  · simp only
    rw [Rep.hom_comm_apply, ha'φ, ← hz, hg]

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
