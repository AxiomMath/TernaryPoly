module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInv
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFour

@[expose] public section



/-! Every alternating four-form is the Hodge star of a one-form: from the involution
`star1to4 (star4to1 a) = (1 / 96) • a` (`star1to4_star4to1_self`), the one-form
`w := 96 • star4to1 a` satisfies `star1to4 w = a`.

Formalized by Claude Sonnet 5.5. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- `star1to4` of the rescaled `star4to1` recovers an alternating four-form. -/
theorem star1to4_star4to1_smul {a : FourCoordinates} (ha : IsAlternatingFour a) :
    star1to4 ((96 : ℝ) • star4to1 a) = a := by
  rw [star1to4_smul]
  funext i j k l
  simp only [Pi.smul_apply]
  rw [star1to4_star4to1_self a ha i j k l, smul_smul]
  norm_num

/-- Every alternating four-form lies in the range of `star1to4`. -/
theorem exists_star1to4_eq {a : FourCoordinates} (ha : IsAlternatingFour a) :
    ∃ w : OneCoordinates, star1to4 w = a :=
  ⟨(96 : ℝ) • star4to1 a, star1to4_star4to1_smul ha⟩

end TernaryPeriodPolynomials.Argument.Coercivity
