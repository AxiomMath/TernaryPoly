module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux01H23
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux01H24
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux01H32
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux01H34
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux01H42
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux01H43

@[expose] public section



/-! First-two-indices-`0,1` slice of the "down-then-up" involution
`star1to4 (star4to1 a) = (1/96) • a` for alternating `a : FourCoordinates`. The six genuinely
pairwise-distinct `(k, l)` branches (`k, l ∈ {2, 3, 4}`, `k ≠ l`) are each discharged by their own lemma (imported above). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_aux01 (a : FourCoordinates) (ha : IsAlternatingFour a)
    (k l : Fin 5) : star1to4 (star4to1 a) 0 1 k l = (1 / 96 : ℝ) • a 0 1 k l := by
  fin_cases k <;> fin_cases l





  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  -- k = 1 (dup via j = 1 = k in all five)
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  -- k = 2
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 0
    decide
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 1
    decide
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 2
    decide
  · exact star1to4_star4to1_self_aux01_23 a ha                     -- l = 3
  · exact star1to4_star4to1_self_aux01_24 a ha                     -- l = 4
  -- k = 3
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 0
    decide
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 1
    decide
  · exact star1to4_star4to1_self_aux01_32 a ha                     -- l = 2
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 3
    decide
  · exact star1to4_star4to1_self_aux01_34 a ha                     -- l = 4
  -- k = 4
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 0
    decide
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 1
    decide
  · exact star1to4_star4to1_self_aux01_42 a ha                     -- l = 2
  · exact star1to4_star4to1_self_aux01_43 a ha                     -- l = 3
  · apply star1to4_star4to1_self_of_dup ha                        -- l = 4
    decide

end TernaryPeriodPolynomials.Argument.Coercivity
