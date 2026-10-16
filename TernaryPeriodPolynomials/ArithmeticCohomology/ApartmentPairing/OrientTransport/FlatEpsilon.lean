module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.Nonvanish2

@[expose] public section


/-!
# The orientation transport for the coefficient dictionary, with non-vanishing

`apartment_orientation_transport`: there are a nonzero rational `κ` with `FlatIntersectionBridge κ` (so that
`ev(z) = (κ · dT0) · coeffAtT0(z)`, `evaluation_eq_coeffAtT0`) and a nonzero rational `τ` — the value of the pulled-back planar Thom
cochain on the chart chain of the flat — such that `d₅ ≠ 0` and

  `κ · dT0 = d₅ · ε`,   `ε := - τ / lam2`.

Here `d₅` is the library degree of the positive product cell (`stair`), and `ε` is minus the degree of the chart chain of the flat
over the positive reference triangle (`flatDegree`).  In the orientation of `M` for which the positive product cell has degree one
(`d₅ = 1`) the dictionary constant is `κ · dT0 = ε`.  Non-vanishing of `lam2`, `d₅`, `τ` follows from `lam2_ne_zero`
(`Nonvanish2`, the planar analogue of the `lamPos_ne_zero`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open CategoryTheory TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPeriodPolynomials.Argument.Lemma33.Retract TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

/-- The degree of a planar chain over the positive reference triangle. -/
def flatDegree (τ : ℚ) : ℚ := τ / lam2

/-- **The orientation transport of Lemma 3.3 for the coefficient dictionary.**
`κ · dT0 = d₅ · ε` with `ε = - flatDegree τ`, all constants nonzero. -/
theorem apartment_orientation_transport :
    ∃ (κ τ : ℚ), κ ≠ 0 ∧ FlatIntersectionBridge κ ∧ d5 ≠ 0 ∧ τ ≠ 0 ∧
      κ * dT0 = d5 * (-(flatDegree τ)) := by
  obtain ⟨κ, τ, hκ, hB, h⟩ := lam2_mul_kappa_dT0
  have hl : lam2 ≠ 0 := lam2_ne_zero
  have hd : dT0 ≠ 0 := dT0_ne_zero
  have hprod : d5 * τ ≠ 0 := by
    intro h0
    rw [h0, neg_zero] at h
    exact mul_ne_zero hl (mul_ne_zero hκ hd) h
  refine ⟨κ, τ, hκ, hB, left_ne_zero_of_mul hprod, right_ne_zero_of_mul hprod, ?_⟩
  unfold flatDegree
  field_simp
  linear_combination h

/-- **The sign of the orientation transport.**  The formal flat chain over the positive reference triangle has degree `1`
(`flatDegree τ = 1`), and the dictionary constant is `κ · dT0 = - d₅`: in the orientation of `M` for which the staircase cell has degree `d₅ = 1`,
the standard top cell has `dT0 = - lamPos`, the formal flat is positively oriented in the log-pivot plane coordinates, and so `ε = - 1`. -/
theorem apartment_orientation_sign :
    ∃ (κ τ : ℚ), κ ≠ 0 ∧ FlatIntersectionBridge κ ∧ flatDegree τ = 1 ∧ κ * dT0 = -d5 := by
  obtain ⟨κ, τ, hκ, hB, h, hτ⟩ := flatIntersectionBridge_value
  have hl : lam2 ≠ 0 := lam2_ne_zero
  have hκd : κ * lamPos = d5 := by
    subst hτ
    exact mul_right_cancel₀ hl (by linear_combination h)
  refine ⟨κ, τ, hκ, hB, ?_, ?_⟩
  · rw [hτ]
    exact div_self hl
  · rw [dT0_eq_neg_lamPos]
    linear_combination -hκd

/-- **The values of the Lemma 3.3 constants.**  The intersection constant is `κ = d₅ / lamPos`
(`κ · lamPos = d₅`) and the dictionary constant is `κ · dT0 = - d₅`, with `d₅`, `lamPos`, `lam2` the non-zero the library
degrees of the staircase product cell, the positive reference tetrahedron and the positive reference triangle. -/
theorem apartment_constant_values :
    ∃ κ : ℚ, κ ≠ 0 ∧ FlatIntersectionBridge κ ∧ κ * lamPos = d5 ∧ κ * dT0 = -d5 ∧
      d5 ≠ 0 ∧ lamPos ≠ 0 ∧ lam2 ≠ 0 := by
  obtain ⟨κ, τ, hκ, hB, h, hτ⟩ := flatIntersectionBridge_value
  have hl : lam2 ≠ 0 := lam2_ne_zero
  have hκd : κ * lamPos = d5 := by
    subst hτ
    exact mul_right_cancel₀ hl (by linear_combination h)
  have hd5 : d5 ≠ 0 := by
    intro h0
    rw [h0] at hκd
    exact mul_ne_zero hκ lamPos_ne_zero hκd
  refine ⟨κ, hκ, hB, hκd, ?_, hd5, lamPos_ne_zero, hl⟩
  rw [dT0_eq_neg_lamPos]
  linear_combination -hκd

/-- **The coefficient dictionary with its explicit constant**: the evaluator of the class of a cellular top cycle is `- d₅`
times its coefficient at the standard top cell `T₀`. -/
theorem apartment_evaluation_eq_neg_d5_coefficient :
    ∀ (W : Rep.{0} ℚ principalSix) (z : (cellCoinv W).X 3) (hz : ((cellCoinv W).d 3 2).hom z = 0),
      (TernaryPoly.OrdinaryTopBoundaryComparison.groupApartmentEvaluation W).hom
          ((cellGroupHomologyMap W 3).hom (cellClass W z hz)) = (-d5) • (coeffAtT0 W).hom z := by
  obtain ⟨κ, -, hB, -, hc, -⟩ := apartment_constant_values
  intro W z hz
  rw [evaluation_eq_coeffAtT0 hB W z hz, hc]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
