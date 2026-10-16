module

public import TernaryPeriodPolynomials.BoundaryComparison.LemmaC3Final
public import TernaryPeriodPolynomials.BoundaryComparison.FiniteEntries
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GoodFlags

@[expose] public section


/-!
# CMP-8 (domain adequacy): `bad_plane_data_injective` is the paper's injectivity for the classical bad-plane seed data

Comparison obligation CMP-8, statement-level half.
The paper's C.6 asserts that the *bad-plane data* (the transfers of the holomorphic and antiholomorphic seeds of `Γ(N)` at a
bad plane) map injectively to a good line under the constant term `T`.  The `bad_plane_data_injective` quantifies over all
inner plane classes vanishing at the good planes.  `Statements.LemmaC3Final.lemma_C3_final_sentence` identifies the two: the inner
classes are, through their Shapiro components at a good and a bad plane, exactly the pairs of transfers of seed spans.  This file
assembles that identification with `bad_plane_data_injective`:

* `vanishesOnGood_of_fixedPointH2_eq_zero_at_good_flag`: vanishing of the Shapiro component at ONE good plane gives
  `VanishesOnGood`.
* `appendix_C6_classical_seeds`: for every class `yb` of the seed span `faceSeedSpan N hb n` at a bad plane there is an inner
  class `ξ` whose component at a good plane `hg` is zero and at `hb` is the transfer of `yb`, and if `T ξ` vanishes at every good
  line then the transfer of `yb` is zero (and `ξ = 0`).

What this does NOT show: that the model's adelic bad-plane sections (`planeSource` of a level-one eigenform datum, the objects of the
entry computation) ARE the classical seed classes.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspOrbits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

/-- **Vanishing at one good flag gives `VanishesOnGood`.** -/
theorem vanishesOnGood_of_fixedPointH2_eq_zero_at_good_flag {n : ℕ} {χ : RankOneCharacter} {side : Side}
    (a : StratumH2 n χ side) {F₀ : Flags side} (hF₀ : GoodFlag side F₀)
    (h : fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F₀ a = 0) : VanishesOnGood n χ side a := by
  refine (vanishesOnGood_iff_fixedPointH2 a).mpr ?_
  intro flag hflag
  obtain ⟨δ, hδ⟩ := cuspFlag_transporter side true F₀ ⟨fun _ => rfl, fun _ => hF₀⟩
  obtain ⟨γ, hγ⟩ := cuspFlag_transporter side true flag ⟨fun _ => rfl, fun _ => hflag⟩
  have hel : (γ * δ⁻¹ : rationalLevel).val • F₀ = flag := by
    rw [← hδ, ← hγ]
    change (γ.val * (δ.val)⁻¹) • (δ.val • cuspFlag side true) = γ.val • cuspFlag side true
    rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have key := stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
    (γ * δ⁻¹) F₀ flag hel a
  rw [h, map_zero] at key
  exact key.symm

open TernaryPeriodPolynomials.Argument.Statements.LemmaC3Final in
/-- **`bad_plane_data_injective` for the classical bad-plane seed data.**  Let `N ≥ 3` with `3 ∣ N`, `T` the line constant
term of Proposition C.5 (`hT`), and `hg`, `hb` integral representatives of a good and a bad rational plane.  For every class `yb` of the
span of the holomorphic and antiholomorphic seeds of `Γ(N)` at the bad plane (`faceSeedSpan N hb n`, the paper's bad-plane data) there
is an inner plane class `ξ` of the level group `K†` whose Shapiro component at the good plane is zero and at the bad plane is the
transfer of `yb`; and if `T ξ` vanishes at every good line then `ξ = 0`, in particular the transfer of `yb` is zero. -/
theorem appendix_C6_classical_seeds (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
      ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        globalCoordinates n trivialCharacter c = (ξ, T ξ))
    (hg hb : SL(3, ℤ)) (hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt hg))
    (hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt hb))
    (yb : groupCohomology.H2 (SeedC3S4c.faceRep N hb n)) (hyb : yb ∈ SeedC3S4c.faceSeedSpan N hb n) :
    ∃ ξ : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ ∧
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hg) ξ = 0 ∧
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hb) ξ =
        SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb ∧
      (VanishesOnGood n trivialCharacter .line (T ξ) → ξ = 0) := by
  obtain ⟨c, hc1, hc2⟩ := (lemma_C3_final_sentence N h3 hN hg hb hgood hbad n).2 0 (Submodule.zero_mem _) yb hyb
  have hξg : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hg)
      c.val = 0 := hc1.trans (map_zero _)
  have hξb : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hb)
      c.val = SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb := hc2
  refine ⟨c.val, c.property, hξg, hξb, fun hline => ?_⟩
  exact TernaryPeriodPolynomials.bad_plane_data_injective n hn T hT c.val c.property
    (vanishesOnGood_of_fixedPointH2_eq_zero_at_good_flag c.val hgood hξg) hline

open TernaryPeriodPolynomials.Argument.Statements.LemmaC3Final in
/-- **The domain of `bad_plane_data_injective` is the classical bad-plane seed data.**  Every inner plane class `ξ` of `K†` has, at a good plane
`hg` and at a bad plane `hb`, Shapiro components that are the transfers of classes of the seed spans of `Γ(N)`
(`lemma_C3_final_sentence` (A)); so the classes `ξ` to which `bad_plane_data_injective` applies are all of this form. -/
theorem inner_components_are_seed_transfers (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ)
    (hg hb : SL(3, ℤ)) (hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt hg))
    (hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt hb))
    (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ yg ∈ SeedC3S4c.faceSeedSpan N hg n, ∃ yb ∈ SeedC3S4c.faceSeedSpan N hb n,
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hg) ξ =
        SeedC3S4c.planeTransfer N h3 hN hg n trivialCharacter yg ∧
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) (SeedC3S4c.planeFlagAt hb) ξ =
        SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb := by
  obtain ⟨yg, hyg, yb, hyb, h1, h2⟩ := (lemma_C3_final_sentence N h3 hN hg hb hgood hbad n).1 ⟨ξ, hξ⟩
  exact ⟨yg, hyg, yb, hyb, h1, h2⟩

end TernaryPeriodPolynomials.Argument.KDaggerComparison
