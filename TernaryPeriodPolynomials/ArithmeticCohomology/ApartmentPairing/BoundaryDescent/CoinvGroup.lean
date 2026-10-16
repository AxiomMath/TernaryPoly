module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.BoundaryDescent.CoinvIso
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Naturality.HLevelMaps

@[expose] public section


/-!
# `H₃(H, E) ≅ H₃(Γ', E)_Δ` for `Γ' = Γ(6) ≤ H`, the group-homology half of the descent

Formalized by Claude Sonnet 5.5.  Proof of Proposition 3.4.

`repN H M` is the conjugation action `c_g = H₃(conj g, ρ g)` of `H` on `H₃(Γ(6)-in-H, Res_H M)` (`Mathlib`'s `groupHomology.map`), a
representation of `H` (`cAct_one`, `cAct_mul`) on which `Γ(6)` acts trivially (`repN_NH`), hence a representation `repDeltaN` of the finite
group `Δ = H/Γ(6)`.  `groupCoinvEquiv`: `Coinvariants (repN H M) ≃ₗ[ℚ] H₃(H, Res_H M)`, `[z] ↦ Cor z`, and `groupCoinvDelta` the same for
`Δ`-coinvariants.  Rational averaging is exact: surjectivity and the kernel of the corestriction come from `corN_surjective`,
`corN_eq_zero_iff`, `corN_cAct` of `GroupHomology.NormalDescent`.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.ModThreeGoodAction Representation
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.Lemma33.Naturality

noncomputable section
namespace TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Act

variable {K : Type} [Group K] (N : Subgroup K) [N.Normal] (A : Rep.{0} ℚ K) (n : ℕ)

theorem GY_of_mem (Y : ChainComplex (Rep.{0} ℚ K) ℕ) (g : K) (hg : g ∈ N) : GY N Y g = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  apply ModuleCat.hom_ext
  exact gamMap_of_mem N (Y.X i).ρ ⟨g, hg⟩

theorem GY_mul (Y : ChainComplex (Rep.{0} ℚ K) ℕ) (g h : K) : GY N Y (g * h) = GY N Y h ≫ GY N Y g := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  apply ModuleCat.hom_ext
  exact gamMap_mul N (Y.X i).ρ g h

theorem cAct_of_mem (g : K) (hg : g ∈ N) : cAct N A n g = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine (iso_hom_bijective (eN N A n)).1 ?_
  rw [eN_cAct N A n, GY_of_mem N _ g hg, homologyMap_id]
  rfl

theorem cAct_one : cAct N A n (1 : K) = LinearMap.id := cAct_of_mem N A n 1 N.one_mem

theorem cAct_mul (g h : K) : cAct N A n (g * h) = cAct N A n g ∘ₗ cAct N A n h := by
  apply LinearMap.ext
  intro z
  refine (iso_hom_bijective (eN N A n)).1 ?_
  rw [LinearMap.comp_apply, eN_cAct N A n, eN_cAct N A n, eN_cAct N A n, GY_mul, homologyMap_comp]
  rfl

end Act

section Rep

variable (H : Subgroup IntegralGL) (V₀ : Rep.{0} ℚ IntegralGL)

/-- **The conjugation action of `H` on `H₃(Γ(6), E)`** (`Γ(6)` realised as `Γ(6)`-in-`H`), `g ↦ c_g = H₃(conj g, ρ g)`. -/
def repN : Representation ℚ ↥H (groupHomology (Rep.res (NH H).subtype (MH H V₀)) 3) where
  toFun g := cAct (NH H) (MH H V₀) 3 g
  map_one' := cAct_one (NH H) (MH H V₀) 3
  map_mul' g h := cAct_mul (NH H) (MH H V₀) 3 g h

theorem repN_apply (g : ↥H) : repN H V₀ g = cAct (NH H) (MH H V₀) 3 g := rfl

/-- `Γ(6)` acts trivially on `H₃(Γ(6), E)` through conjugation. -/
instance repN_trivial : IsTrivial ((repN H V₀).comp (NH H).subtype) :=
  ⟨fun n => cAct_of_mem (NH H) (MH H V₀) 3 n.1 n.2⟩

/-- The action of the finite group `Δ = H/Γ(6)` on `H₃(Γ(6), E)`. -/
def repDeltaN : Representation ℚ (↥H ⧸ NH H) (groupHomology (Rep.res (NH H).subtype (MH H V₀)) 3) :=
  ofQuotient (repN H V₀) (NH H)

theorem avgN_eq_avgR : avgN (NH H) (MH H V₀) 3 = avgR (NH H) (repN H V₀) := rfl

/-- **`H₃(H, E) ≅ H₃(Γ', E)_H`**: the corestriction `H₃(Γ(6), E) → H₃(H, E)` induces a linear isomorphism from the coinvariants of the
conjugation action (rational averaging is exact). -/
def groupCoinvEquiv : Coinvariants (repN H V₀) ≃ₗ[ℚ] groupHomology (MH H V₀) 3 :=
  coinvEquiv (NH H) (repN H V₀) (corN (NH H) (MH H V₀) 3)
    (corN_surjective (A := MH H V₀) (n := 3) (card_ne_zero_NH H))
    (fun g z => corN_cAct (N := NH H) (A := MH H V₀) (n := 3) g z)
    (fun z hz => (corN_eq_zero_iff (A := MH H V₀) (n := 3) (card_ne_zero_NH H) z).mp hz)

@[simp]
theorem groupCoinvEquiv_mk (z : groupHomology (Rep.res (NH H).subtype (MH H V₀)) 3) :
    groupCoinvEquiv H V₀ (Coinvariants.mk (repN H V₀) z) = corN (NH H) (MH H V₀) 3 z := rfl

/-- **`H₃(H, E) ≅ H₃(Γ', E)_Δ`** with `Δ = H/Γ'`. -/
def groupCoinvDelta : Coinvariants (repDeltaN H V₀) ≃ₗ[ℚ] groupHomology (MH H V₀) 3 :=
  coinvQuotEquiv (NH H) (repN H V₀) (corN (NH H) (MH H V₀) 3)
    (corN_surjective (A := MH H V₀) (n := 3) (card_ne_zero_NH H))
    (fun g z => corN_cAct (N := NH H) (A := MH H V₀) (n := 3) g z)
    (fun z hz => (corN_eq_zero_iff (A := MH H V₀) (n := 3) (card_ne_zero_NH H) z).mp hz)

@[simp]
theorem groupCoinvDelta_mk (z : groupHomology (Rep.res (NH H).subtype (MH H V₀)) 3) :
    groupCoinvDelta H V₀ (Coinvariants.mk (repDeltaN H V₀) z) = corN (NH H) (MH H V₀) 3 z := rfl

end Rep

end TernaryPeriodPolynomials.Argument.Lemma33.BoundaryDescent
