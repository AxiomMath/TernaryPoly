module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.ZeroFive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleFiveB
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.RuleIsometryFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourRepr

@[expose] public section



/-! The degree-four energy split for `algebraicHodgeFour`, mirroring
`CoercivityOne.Algebra.algebraicHodgeOne_energy` one level up and reusing
`exteriorThree_contractionFour_adjoint` (`HodgeFour.lean`) for the first summand, together with
`fourPairing_add_left` (`HodgeThree.lean`). The second summand needs the top-degree adjunction
`exteriorFour_contractionFive_adjoint`, proved by Hodge-star transport to the degree-zero
adjunction `exteriorZero_contractionOne_adjoint` (with a `1 / 96` correction coming from the star
isometry).

Formalized by Claude Sonnet 5.5. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

theorem fourPairing_symmetric (a b : FourCoordinates) : fourPairing a b = fourPairing b a := by
  simp only [fourPairing, factorialPairing_symmetric]

/-- Degree-four/top adjunction between `exteriorFour` and `contractionFive` against
`fourPairing`/`factorialPairing`, mirroring `exteriorZero_contractionOne_adjoint`
(`CoercivityOne/Algebra.lean`) at the other boundary of the complex. Proof by Hodge-star
transport: every alternating four-form is `star1to4 w` (`exists_star1to4_eq`), and the lemmas
`contractionFive_star1to4`, `exteriorFour_star1to4`, `hodgeStarRule_isometry_degree_four` reduce the
claim to the degree-zero adjunction `exteriorZero_contractionOne_adjoint`. -/
theorem exteriorFour_contractionFive_adjoint (a : FourCoordinates) (ha : IsAlternatingFour a)
    (b : Poly) :
    fourPairing a (contractionFive b) = (1 / 96 : ℝ) * factorialPairing (exteriorFour a) b := by
  obtain ⟨w, rfl⟩ := exists_star1to4_eq ha
  rw [contractionFive_star1to4, hodgeStarRule_isometry_degree_four, exteriorFour_star1to4,
    onePairing_symmetric, exteriorZero_contractionOne_adjoint, factorialPairing_symmetric b]

/-- The energy identity for the degree-four algebraic Hodge operator, mirroring
`algebraicHodgeOne_energy` one level up: the first summand's adjunction
(`exteriorThree_contractionFour_adjoint`) applies directly, and the second needs a
`fourPairing_symmetric` flip before `exteriorFour_contractionFive_adjoint` closes it. -/
theorem algebraicHodgeFour_energy (a : FourCoordinates) (ha : IsAlternatingFour a) :
    fourPairing (algebraicHodgeFour a) a =
      threePairing (contractionFour a) (contractionFour a) +
        (1 / 96 : ℝ) * factorialPairing (exteriorFour a) (exteriorFour a) := by
  rw [algebraicHodgeFour, fourPairing_add_left, exteriorThree_contractionFour_adjoint _ a ha,
    fourPairing_symmetric (contractionFive (exteriorFour a)) a,
    exteriorFour_contractionFive_adjoint a ha]

end TernaryPeriodPolynomials.Argument.Coercivity
