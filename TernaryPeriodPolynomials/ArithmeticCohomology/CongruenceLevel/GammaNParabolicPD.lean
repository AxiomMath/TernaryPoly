module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.GammaN

@[expose] public section


/-!
# Perfect duality `ker d_c(E) × C¹(E^∨)/δC⁰(E^∨)` for `Γ(N)` in the dual Farey-tree model

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

`gammaN_parabolic_pairing` is the pairing on the images of the *naive* edge-identity map
`j_comb : ker d_c → C¹/δC⁰` (see `gammaN_naive_parabolic_pairing`, the same statement under its correct name).  It is **NOT** the
topological map `H¹_c → H¹` and **NOT** the paper's cuspidal pairing: it is symmetric (the paper's cup product is skew), and for trivial
coefficients `dim Im j_comb = 2g + c - 1` (cuspidal cohomology has dimension `2g`).

What is proved, and is the genuine content, for `N ≥ 3` and every finite-dimensional complex representation `E` of `Γ(N) ≤ GL₂(ℤ)`
(with dual `E^∨`), in the Farey cochain model (`C⁰` = equivariant functions on triangles, `C¹` = antisymmetric equivariant functions on
oriented dual edges, `δ : C⁰ → C¹`, `d_c : C¹ → C⁰`, so `C¹/δC⁰ = H¹(Γ(N), E)` in the dual-tree model and `ker d_c = H¹_c`):

1. `gammaN_poincare_duality_c`/`_q`: the annihilator of `ker d_c(E)` in `C¹(E^∨)` is exactly `δ C⁰(E^∨)` and conversely, i.e. the pairing
   `ker d_c(E) × C¹(E^∨)/δC⁰(E^∨) → ℂ` is perfect (adjointness `⟨F, δH⟩ = -2⟨d_c F, H⟩` of the orbit pairing).
2. `gammaN_naive_parabolic_pairing` (= `gammaN_parabolic_pairing`): the abstract Lefschetz pairing of the NAIVE pair `(j_comb, j_comb')`.

Not proved here: the identification of `C¹/δC⁰` with `groupCohomology.H1`, the topological `j`, the cuspidal pairing.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPoly.RankTwoAugmentedFrames

/-- Poincaré duality, first half: a class of `C¹(E^∨)` killing every compactly supported cocycle of `E` is a coboundary. -/
theorem gammaN_poincare_duality_c {N : ℕ} (hN : 3 ≤ N) {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (gammaNGL N) E) (G : C1 ρ.dual)
    (hG : ∀ F : C1 ρ, dc ρ F = 0 → pV (dualCoupling ρ) (gammaNFareyData hN) F G = 0) : G ∈ LinearMap.range (delta ρ.dual) :=
  annihilator_ker_dc (dualCoupling ρ) (gammaNFareyData hN) G hG

/-- Poincaré duality, second half: a class of `C¹(E)` killing every compactly supported cocycle of `E^∨` is a coboundary. -/
theorem gammaN_poincare_duality_q {N : ℕ} (hN : 3 ≤ N) {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (gammaNGL N) E) (F : C1 ρ)
    (hF : ∀ G : C1 ρ.dual, dc ρ.dual G = 0 → pV (dualCoupling ρ) (gammaNFareyData hN) F G = 0) : F ∈ LinearMap.range (delta ρ) :=
  annihilator_ker_dc' (dualCoupling ρ) (gammaNFareyData hN) F hF

/-- **CORRECTED DOCSTRING.** The pairing of `Γ(N)`, `N ≥ 3`, on the images of the NAIVE edge-identity map `j_comb : ker d_c → C¹/δC⁰` is well
defined and nondegenerate on both sides.  This is NOT the topological `H¹_c → H¹` and NOT the paper's cuspidal pairing (it is symmetric;
`dim Im j_comb = 2g + c - 1`).  See `gammaN_naive_parabolic_pairing`. -/
theorem gammaN_parabolic_pairing {N : ℕ} (hN : 3 ≤ N) {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (gammaNGL N) E) :
    (∀ (a : Hc ρ) (b : Hc ρ.dual),
      parabolicPairing (dualCoupling ρ) (gammaNFareyData hN) ⟨jmap ρ a, LinearMap.mem_range_self _ a⟩
          ⟨jmap ρ.dual b, LinearMap.mem_range_self _ b⟩ = pV (dualCoupling ρ) (gammaNFareyData hN) a.1 b.1) ∧
    (∀ x : LinearMap.range (jmap ρ), (∀ y, parabolicPairing (dualCoupling ρ) (gammaNFareyData hN) x y = 0) → x = 0) ∧
    (∀ y : LinearMap.range (jmap ρ.dual), (∀ x, parabolicPairing (dualCoupling ρ) (gammaNFareyData hN) x y = 0) → y = 0) :=
  ⟨parabolicPairing_apply _ _, parabolicPairing_left_nondegenerate _ _, parabolicPairing_right_nondegenerate _ _⟩

/-- The same statement as `gammaN_parabolic_pairing` under its correct name: nondegeneracy of the pairing on the images of the NAIVE map
`j_comb : ker d_c → C¹/δC⁰`.  It is not the paper's cuspidal pairing (symmetric versus skew; `dim Im j_comb = 2g + c - 1`). -/
theorem gammaN_naive_parabolic_pairing {N : ℕ} (hN : 3 ≤ N) {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (gammaNGL N) E) :
    (∀ x : LinearMap.range (naiveJ ρ), (∀ y, naiveParabolicPairing (dualCoupling ρ) (gammaNFareyData hN) x y = 0) → x = 0) ∧
    (∀ y : LinearMap.range (naiveJ ρ.dual), (∀ x, naiveParabolicPairing (dualCoupling ρ) (gammaNFareyData hN) x y = 0) → y = 0) :=
  (gammaN_parabolic_pairing hN ρ).2

end TernaryPeriodPolynomials.Argument.Statements.GammaNParabolicPD
