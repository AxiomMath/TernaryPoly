module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.AbsCoinv

@[expose] public section


/-!
# Recognising a quotient as the coinvariants of a finite quotient action (abstract)

Formalized by Claude Sonnet 5.5.  Proof of Proposition 3.4,
("Rational Hochschild--Serre and averaging give `H₃(K,E) ≅ H₃(Γ',E)_Δ`.  The same finite-cover descent applies to boundary homology").

Let `ρ` be a representation of `Γ` on a `ℚ`-module `B`, `N ⊴ Γ` of finite index, and `f : B → C` a surjective `Γ`-invariant linear map
whose kernel is contained in the kernel of the averaging operator `avgR N ρ`.  Then `f` induces a linear isomorphism
`Coinvariants ρ ≃ₗ[ℚ] C` (`coinvEquiv`), `mk z ↦ f z`.  If moreover `N` acts trivially, `ρ` descends to a representation of the finite group
`Δ = Γ/N` (`Representation.ofQuotient`) and `coinvQuotEquiv` is the isomorphism `Coinvariants (ρ̄ : Δ) ≃ₗ[ℚ] C`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

open Representation TernaryPeriodPolynomials.Argument.Lemma33.Naturality
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Abs

variable {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal] [N.FiniteIndex]
  {B C : Type*} [AddCommGroup B] [Module ℚ B] [AddCommGroup C] [Module ℚ C] (ρ : Representation ℚ Γ B)

theorem comp_eq_of_invariant (f : B →ₗ[ℚ] C) (hinv : ∀ g z, f (ρ g z) = f z) (g : Γ) : f ∘ₗ ρ g = f :=
  LinearMap.ext (hinv g)

/-- **Recognition of the coinvariants**: a surjective invariant map whose kernel lies in the kernel of the `Γ/N`-average induces
`Coinvariants ρ ≃ₗ[ℚ] C`. -/
def coinvEquiv (f : B →ₗ[ℚ] C) (hsurj : Function.Surjective f) (hinv : ∀ g z, f (ρ g z) = f z)
    (hker : ∀ z, f z = 0 → avgR N ρ z = 0) : Coinvariants ρ ≃ₗ[ℚ] C :=
  LinearEquiv.ofBijective (Coinvariants.lift ρ f (comp_eq_of_invariant ρ f hinv)) (by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      obtain ⟨z, rfl⟩ := Coinvariants.mk_surjective ρ w
      rw [Coinvariants.lift_mk] at hw
      rw [← mk_avgR (N := N) (ρ := ρ) z, hker z hw, map_zero]
    · intro c
      obtain ⟨z, rfl⟩ := hsurj c
      exact ⟨Coinvariants.mk ρ z, Coinvariants.lift_mk ρ _ _ z⟩)

omit [N.Normal] in
@[simp]
theorem coinvEquiv_mk (f : B →ₗ[ℚ] C) (hsurj : Function.Surjective f) (hinv : ∀ g z, f (ρ g z) = f z)
    (hker : ∀ z, f z = 0 → avgR N ρ z = 0) (z : B) :
    coinvEquiv N ρ f hsurj hinv hker (Coinvariants.mk ρ z) = f z := rfl

omit [N.FiniteIndex] in
/-- The `Γ`-invariants-generating submodule of a representation factoring through `Γ/N` is the one of the quotient representation. -/
theorem ker_ofQuotient (ρ : Representation ℚ Γ B) [IsTrivial (ρ.comp N.subtype)] :
    Coinvariants.ker (ofQuotient ρ N) = Coinvariants.ker ρ := by
  unfold Coinvariants.ker
  congr 1
  ext x
  constructor
  · rintro ⟨⟨q, v⟩, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨(g, v), rfl⟩
  · rintro ⟨⟨g, v⟩, rfl⟩
    exact ⟨((g : Γ ⧸ N), v), rfl⟩

/-- The coinvariants of the quotient representation of `Δ = Γ/N` are those of `ρ`. -/
def coinvQuotIso [IsTrivial (ρ.comp N.subtype)] : Coinvariants (ofQuotient ρ N) ≃ₗ[ℚ] Coinvariants ρ :=
  Submodule.quotEquivOfEq _ _ (ker_ofQuotient N ρ)

omit [N.FiniteIndex] in
theorem coinvQuotIso_mk [IsTrivial (ρ.comp N.subtype)] (z : B) :
    coinvQuotIso N ρ (Coinvariants.mk (ofQuotient ρ N) z) = Coinvariants.mk ρ z := rfl

/-- **The coinvariants of the finite quotient group `Δ = Γ/N`** (`N` acting trivially) are the recognised quotient. -/
def coinvQuotEquiv [IsTrivial (ρ.comp N.subtype)] (f : B →ₗ[ℚ] C) (hsurj : Function.Surjective f)
    (hinv : ∀ g z, f (ρ g z) = f z) (hker : ∀ z, f z = 0 → avgR N ρ z = 0) :
    Coinvariants (ofQuotient ρ N) ≃ₗ[ℚ] C :=
  (coinvQuotIso N ρ).trans (coinvEquiv N ρ f hsurj hinv hker)

@[simp]
theorem coinvQuotEquiv_mk [IsTrivial (ρ.comp N.subtype)] (f : B →ₗ[ℚ] C) (hsurj : Function.Surjective f)
    (hinv : ∀ g z, f (ρ g z) = f z) (hker : ∀ z, f z = 0 → avgR N ρ z = 0) (z : B) :
    coinvQuotEquiv N ρ f hsurj hinv hker (Coinvariants.mk (ofQuotient ρ N) z) = f z := rfl

end Abs

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
