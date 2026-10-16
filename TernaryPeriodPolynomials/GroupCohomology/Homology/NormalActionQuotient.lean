module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalAction

@[expose] public section


/-!
# Quotient actions on the third term of a short exact sequence

If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence of chain complexes of `H`-representations with a
`G`-action on `X₁` and `X₂` (compatible with `f`), and `g : X₂ → X₃` has a degreewise
`H`-equivariant splitting `s`, then `X₃` inherits a `G`-action making `g` equivariant:
`ρ₃(γ) = g ∘ ρ₂(γ) ∘ s`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory

section Quotient

variable {G : Type} [Group G] {H : Subgroup G} [H.Normal]

local instance : HasForget₂ (Rep.{0} ℚ ↥H) Ab.{0} :=
  HasForget₂.trans (Rep ℚ ↥H) (ModuleCat ℚ) Ab
local instance : (forget₂ (Rep.{0} ℚ ↥H) Ab.{0}).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ ↥H) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)
local instance : (forget₂ (Rep.{0} ℚ ↥H) Ab.{0}).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ ↥H) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

variable {S : ShortComplex (ChainComplex (Rep.{0} ℚ ↥H) ℕ)} (hS : S.ShortExact)
  {A₁ : GActC S.X₁} {A₂ : GActC S.X₂} (hf : IsGMorC A₁ A₂ S.f)

include hS hf in
/-- The kernel of `g` is stable under the `G`-action on `X₂`. -/
theorem ker_stable (g : G) (n : ℕ) (x : S.X₂.X n) (hx : S.g.f n x = 0) :
    S.g.f n ((A₂.act n).ρ g x) = 0 := by
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  obtain ⟨w, hw⟩ := (ShortComplex.exact_iff_of_hasForget _).mp (hdeg n).exact x hx
  have hw' : S.f.f n w = x := hw
  have h := hf n g w
  have h0 : S.f.f n ≫ S.g.f n = 0 := by rw [← HomologicalComplex.comp_f, S.zero]; simp
  have h1 := congrArg (fun m => m ((A₁.act n).ρ g w)) h0
  rw [← hw', ← h]
  exact h1

variable (s : ∀ n, S.X₃.X n ⟶ S.X₂.X n) (hs : ∀ n, s n ≫ S.g.f n = 𝟙 _)

omit [H.Normal] hS hf in
theorem gs_apply {s : ∀ n, S.X₃.X n ⟶ S.X₂.X n} (hs : ∀ n, s n ≫ S.g.f n = 𝟙 _) (n : ℕ)
    (y : S.X₃.X n) : S.g.f n ((s n) y) = y :=
  congrArg (fun m => m y) (hs n)

include hS hf hs in
/-- Pushing a representative forward and back does not change the image under `g`. -/
theorem core (g : G) (n : ℕ) (x : S.X₂.X n) :
    S.g.f n ((A₂.act n).ρ g (s n (S.g.f n x))) = S.g.f n ((A₂.act n).ρ g x) := by
  have h : S.g.f n (x - s n (S.g.f n x)) = 0 := by
    rw [map_sub, gs_apply hs, sub_self]
  have h2 := ker_stable hS hf g n _ h
  rw [map_sub, map_sub, sub_eq_zero] at h2
  exact h2.symm

/-- The quotient action `ρ₃(γ) = g ∘ ρ₂(γ) ∘ s`. -/
def GActC.quotient : GActC S.X₃ where
  act n :=
    { ρ :=
        { toFun := fun γ => (S.g.f n).hom.toLinearMap ∘ₗ (A₂.act n).ρ γ ∘ₗ (s n).hom.toLinearMap
          map_one' := by
            apply LinearMap.ext
            intro y
            change S.g.f n ((A₂.act n).ρ 1 (s n y)) = y
            rw [map_one]
            exact gs_apply hs n y
          map_mul' := fun γ δ => by
            apply LinearMap.ext
            intro y
            change S.g.f n ((A₂.act n).ρ (γ * δ) (s n y)) =
              S.g.f n ((A₂.act n).ρ γ (s n (S.g.f n ((A₂.act n).ρ δ (s n y)))))
            rw [core hS hf s hs, map_mul]
            rfl }
      conj := fun γ h y => by
        change S.g.f n ((A₂.act n).ρ γ (s n ((S.X₃.X n).ρ h y))) =
          (S.X₃.X n).ρ (conjElt H γ h) (S.g.f n ((A₂.act n).ρ γ (s n y)))
        rw [Rep.hom_comm_apply (s n) h y, (A₂.act n).conj,
          Rep.hom_comm_apply (S.g.f n) (conjElt H γ h)] }
  comm γ n m y := by
    have hg : ∀ x : S.X₂.X n, (S.X₃.d n m).hom (S.g.f n x) = S.g.f m ((S.X₂.d n m).hom x) :=
      fun x => congrArg (fun f => f.hom x) (S.g.comm n m)
    have hu : S.g.f m ((S.X₂.d n m).hom (s n y) - s m ((S.X₃.d n m).hom y)) = 0 := by
      rw [map_sub, ← hg, gs_apply hs n y, gs_apply hs m, sub_self]
    have h2 := ker_stable hS hf γ m _ hu
    rw [map_sub, map_sub, sub_eq_zero] at h2
    change (S.X₃.d n m).hom (S.g.f n ((A₂.act n).ρ γ (s n y))) =
      S.g.f m ((A₂.act m).ρ γ (s m ((S.X₃.d n m).hom y)))
    rw [hg, A₂.comm]
    exact h2

include hS hf hs in
/-- The map `g` is equivariant for the quotient action. -/
theorem GActC.isGMorC_quotient : IsGMorC A₂ (GActC.quotient hS hf s hs) S.g := fun n γ x =>
  (core hS hf s hs γ n x).symm

end Quotient

end TernaryPeriodPolynomials.Argument.GroupHomology
