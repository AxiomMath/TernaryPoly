module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PairValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Bridge

@[expose] public section


/-!
# The flat-intersection bridge with its orientation constant

`flatIntersectionBridge_value`: there are a nonzero rational `κ` with `FlatIntersectionBridge κ` and a rational `τ` — the value of the
pulled-back planar Thom cochain on the chart chain of the flat — with

  `κ · lamPos · lam2 = d₅ · τ`,

where `d₅` is the library degree of the staircase product cell (`stair`) and `lamPos`, `lam2` are the library degrees of the positive
reference tetrahedron and triangle.  Since `dT0 = - lamPos` (`dT0_eq_neg_lamPos`) this is the orientation transport
`lam2 · (κ · dT0) = - d₅ · τ` for the coefficient dictionary `ev(z) = (κ · dT0) · coeffAtT0(z)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open CategoryTheory TernaryPoly.OrdinaryTopBoundaryComparison TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology
  TernaryPeriodPolynomials.Argument.Lemma33.Retract TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Orient TernaryPoly.IntegralGL3Congruence
  TernaryPeriodPolynomials.Argument.Lemma33.Locality

/-- **The universal ratio with its value.** -/
theorem exists_universal_ratio_value :
    ∃ (r τ : ℚ), r ≠ 0 ∧ d5 * r * τ = lamPos * lam2 ∧ τ = lam2 ∧
      ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3)
        (hz : ((cellCoinv W).d 3 2).hom z = 0),
        (intersectionSum W).hom z =
          r • (groupApartmentEvaluation W).hom ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) := by
  have hex : ∃ x, (groupApartmentEvaluation ordinaryCyclesRep).hom x ≠ 0 := by
    by_contra h
    push Not at h
    apply groupApartmentEvaluation_ne_zero
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact h x
  obtain ⟨x, hx⟩ := hex
  obtain ⟨y, rfl⟩ := cellGroupHomologyMap_surjective ordinaryCyclesRep x
  obtain ⟨z₀, hz₀, rfl⟩ := exists_cellClass ordinaryCyclesRep y
  obtain ⟨r₀, τ₀, h₀, -, hval, hτ₀⟩ := pair_relation_value ordinaryCyclesRep ordinaryCyclesRep z₀ hz₀ z₀ hz₀ hx
  have hr0 : r₀ ≠ 0 := by
    intro hr
    rw [hr, zero_smul] at h₀
    have h1 : dT0 • (coeffAtT0 ordinaryCyclesRep).hom z₀ = 0 := h₀
    have h2 : (coeffAtT0 ordinaryCyclesRep).hom z₀ = 0 :=
      (smul_eq_zero.mp h1).resolve_left dT0_ne_zero
    exact hx (evaluation_eq_zero_of_coeff_zero ordinaryCyclesRep z₀ hz₀ h2)
  refine ⟨r₀, τ₀, hr0, hval, hτ₀, ?_⟩
  intro W z hz
  obtain ⟨r, _, h₁, h₂, -, -⟩ := pair_relation_value W ordinaryCyclesRep z hz z₀ hz₀ hx
  have hr : r = r₀ := smul_left_injective ℚ hx (h₂.symm.trans h₀)
  rw [h₁, hr]

/-- **The global bridge with its orientation constant.** -/
theorem flatIntersectionBridge_value :
    ∃ (κ τ : ℚ), κ ≠ 0 ∧ FlatIntersectionBridge κ ∧ κ * lamPos * lam2 = d5 * τ ∧ τ = lam2 := by
  obtain ⟨r, τ, hr, hval, hτ, h⟩ := exists_universal_ratio_value
  refine ⟨r⁻¹, τ, inv_ne_zero hr, ?_, ?_, hτ⟩
  · intro W z hz
    rw [h W z hz, smul_smul, inv_mul_cancel₀ hr, one_smul]
  · calc r⁻¹ * lamPos * lam2 = r⁻¹ * (lamPos * lam2) := by ring
      _ = r⁻¹ * (d5 * r * τ) := by rw [hval]
      _ = d5 * τ := by field_simp

/-- **The orientation transport for the coefficient dictionary.**  With `κ` as above, `lam2 · (κ · dT0) = - d₅ · τ`. -/
theorem lam2_mul_kappa_dT0 :
    ∃ (κ τ : ℚ), κ ≠ 0 ∧ FlatIntersectionBridge κ ∧ lam2 * (κ * dT0) = -(d5 * τ) := by
  obtain ⟨κ, τ, hκ, hB, h, -⟩ := flatIntersectionBridge_value
  refine ⟨κ, τ, hκ, hB, ?_⟩
  rw [dT0_eq_neg_lamPos]
  linear_combination (-1 : ℚ) * h

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
