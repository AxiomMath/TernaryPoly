module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.CoinvIso
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevelMaps

@[expose] public section


/-!
# The same descent for boundary homology: `H₃(∂X̄_H; 𝓜) ≅ H₃(∂X̄_{Γ(6)}; 𝓜)_Δ`

Formalized by Claude Sonnet 5.5.  Proof of Proposition 3.4.

`QbdH H V₀` is the paper's `H₃(∂X̄_H; 𝓜)`, the homology of the `H`-coinvariants of the singular boundary chains (`Naturality.HLevel`).
`repBd V₀ H` is the geometric action of `H` on the neat-level boundary homology `Bd V₀ = H₃(∂X̄_{Γ(6)}; 𝓜)`, trivial on `Γ(6)`
(`repBd_NH`).  `boundaryCoinvEquiv : Coinvariants (repBd V₀ H) ≃ₗ[ℚ] QbdH H V₀`, `[c] ↦ qBdH c`, and `boundaryCoinvDelta` for `Δ = H/Γ(6)`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction Representation
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Boundary

variable (H : Subgroup IntegralGL) (hH : principalSix ≤ H) (V₀ : Rep.{0} ℚ IntegralGL)

/-- `Γ(6)` acts trivially on neat-level boundary homology. -/
instance repBd_trivial : IsTrivial ((repBd V₀ H).comp (NH H).subtype) :=
  ⟨fun n => repBd_NH V₀ H n⟩

/-- The action of the finite group `Δ = H/Γ(6)` on `H₃(∂X̄_{Γ(6)}; 𝓜)`. -/
def repDeltaBd : Representation ℚ (↥H ⧸ NH H) (Bd V₀) :=
  ofQuotient (repBd V₀ H) (NH H)

theorem qBdH_invariant (g : ↥H) (c : Bd V₀) : (qBdH H hH V₀).hom (repBd V₀ H g c) = (qBdH H hH V₀).hom c :=
  qBdH_bAct H hH V₀ g c

/-- **`H₃(∂X̄_H; 𝓜) ≅ H₃(∂X̄_{Γ(6)}; 𝓜)_H`**: the quotient map `qBdH` induces a linear isomorphism from the coinvariants of the
geometric action (rational averaging is exact). -/
def boundaryCoinvEquiv : Coinvariants (repBd V₀ H) ≃ₗ[ℚ] QbdH H V₀ :=
  coinvEquiv (NH H) (repBd V₀ H) (qBdH H hH V₀).hom (qBdH_surjective H hH V₀) (qBdH_invariant H hH V₀)
    (fun z hz => (qBdH_ker H hH V₀ z).mp hz)

@[simp]
theorem boundaryCoinvEquiv_mk (c : Bd V₀) :
    boundaryCoinvEquiv H hH V₀ (Coinvariants.mk (repBd V₀ H) c) = (qBdH H hH V₀).hom c := rfl

/-- **`H₃(∂X̄_H; 𝓜) ≅ H₃(∂X̄_{Γ(6)}; 𝓜)_Δ`** with `Δ = H/Γ(6)`. -/
def boundaryCoinvDelta : Coinvariants (repDeltaBd H V₀) ≃ₗ[ℚ] QbdH H V₀ :=
  coinvQuotEquiv (NH H) (repBd V₀ H) (qBdH H hH V₀).hom (qBdH_surjective H hH V₀) (qBdH_invariant H hH V₀)
    (fun z hz => (qBdH_ker H hH V₀ z).mp hz)

@[simp]
theorem boundaryCoinvDelta_mk (c : Bd V₀) :
    boundaryCoinvDelta H hH V₀ (Coinvariants.mk (repDeltaBd H V₀) c) = (qBdH H hH V₀).hom c := rfl

end Boundary

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
