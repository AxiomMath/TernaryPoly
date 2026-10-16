module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFour

@[expose] public section



/-! The UNCONDITIONAL "up-then-down" self-identity `star4to1 (star1to4 β) = (1 / 96) • β`,
needed for `hodgeStarRule_isometry_degree_four`. No alternation hypothesis on `β`, since
`OneCoordinates` carries no alternation predicate: expanding both sums, the outer
`eps5 i j k l m` forces `m` to be the unique index completing `{i, j, k, l}` to all of `Fin 5`
(vanishing otherwise), and the surviving contraction is a rank-one Kronecker-delta pairing,
needing no antisymmetrization of `β`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

private theorem star4to1_star1to4_self_apply_0 (β : OneCoordinates) :
    star4to1 (star1to4 β) 0 = (1 / 96 : ℝ) • β 0 := by
  simp only [star4to1, Fin.sum_univ_five]
  simp [tangentWeight, star1to4_eq_single_of_ne (i := 0)]
  module

private theorem star4to1_star1to4_self_apply_1 (β : OneCoordinates) :
    star4to1 (star1to4 β) 1 = (1 / 96 : ℝ) • β 1 := by
  simp only [star4to1, Fin.sum_univ_five]
  simp [tangentWeight, star1to4_eq_single_of_ne (i := 1)]
  module

private theorem star4to1_star1to4_self_apply_2 (β : OneCoordinates) :
    star4to1 (star1to4 β) 2 = (1 / 96 : ℝ) • β 2 := by
  simp only [star4to1, Fin.sum_univ_five]
  simp [tangentWeight, star1to4_eq_single_of_ne (i := 2)]
  module

private theorem star4to1_star1to4_self_apply_3 (β : OneCoordinates) :
    star4to1 (star1to4 β) 3 = (1 / 96 : ℝ) • β 3 := by
  simp only [star4to1, Fin.sum_univ_five]
  simp [tangentWeight, star1to4_eq_single_of_ne (i := 3)]
  module

private theorem star4to1_star1to4_self_apply_4 (β : OneCoordinates) :
    star4to1 (star1to4 β) 4 = (1 / 96 : ℝ) • β 4 := by
  simp only [star4to1, Fin.sum_univ_five]
  simp [tangentWeight, star1to4_eq_single_of_ne (i := 4)]
  module

theorem star4to1_star1to4_self (β : OneCoordinates) :
    star4to1 (star1to4 β) = (1 / 96 : ℝ) • β := by
  funext i
  fin_cases i
  · exact star4to1_star1to4_self_apply_0 β
  · exact star4to1_star1to4_self_apply_1 β
  · exact star4to1_star1to4_self_apply_2 β
  · exact star4to1_star1to4_self_apply_3 β
  · exact star4to1_star1to4_self_apply_4 β

end TernaryPeriodPolynomials.Argument.Coercivity
