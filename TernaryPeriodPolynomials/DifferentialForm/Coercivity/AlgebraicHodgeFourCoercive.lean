module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourRepr
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleCompositeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleIsometryFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.CasimirOne

@[expose] public section



/-! Degree-four basepoint coercivity of `algebraicHodgeFour`, transported from
`homogeneousHodgeOne_coercive` through the Hodge star `star1to4` (isometry up to `1/96`,
composite rule `algebraicHodgeFour ∘ star1to4 = star1to4 ∘ algebraicHodgeOne`, and the
involution `star1to4 ∘ star4to1 = (1/96) • id` on alternating four-forms). This is the
degree-four analogue of `HodgeThreeCoercive.lean`.

Formalized by Claude Sonnet 5.5. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

/-- Degree-four basepoint coercivity of `algebraicHodgeFour`. -/
theorem algebraicHodgeFour_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : FourCoordinates, IsAlternatingFour a →
      (∀ i j k l, (a i j k l).IsHomogeneous n) →
      c * fourPairing a a ≤ fourPairing (algebraicHodgeFour a) a := by
  obtain ⟨c, hc, h⟩ := homogeneousHodgeOne_coercive hn
  refine ⟨c, hc, fun a ha hha => ?_⟩
  let w : OneCoordinates := (96 : ℝ) • star4to1 a
  have hw_hom : w ∈ homogeneousOneForms n := fun p =>
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).smul_mem 96 (star4to1_isHomogeneous a hha p)
  have haw : star1to4 w = a := star1to4_star4to1_smul ha
  have hiso1 : fourPairing a a = (1 / 96 : ℝ) * onePairing w w := by
    rw [← haw, hodgeStarRule_isometry_degree_four w w]
  have hiso2 : fourPairing (algebraicHodgeFour a) a =
      (1 / 96 : ℝ) * onePairing (algebraicHodgeOne w) w := by
    rw [← haw, algebraicHodgeFour_star1to4 w,
      hodgeStarRule_isometry_degree_four (algebraicHodgeOne w) w]
  have hraw : c * onePairing w w ≤ onePairing (algebraicHodgeOne w) w := h ⟨w, hw_hom⟩
  rw [hiso1, hiso2]
  nlinarith

end TernaryPeriodPolynomials.Argument.Coercivity
