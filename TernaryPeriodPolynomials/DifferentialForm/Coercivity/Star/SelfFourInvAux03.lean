module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux03H12
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux03H14
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux03H21
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux03H24
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux03H41
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux03H42

@[expose] public section



/-! First-two-indices-`0,3` slice of the "down-then-up" involution
`star1to4 (star4to1 a) = (1/96) • a` for alternating `a : FourCoordinates`. The six genuinely
pairwise-distinct `(k, l)` branches (`k, l ∈ {1, 2, 4}`, `k ≠ l`) are each discharged by
their own lemma (imported above).



-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_aux03 (a : FourCoordinates) (ha : IsAlternatingFour a)
    (k l : Fin 5) : star1to4 (star4to1 a) 0 3 k l = (1 / 96 : ℝ) • a 0 3 k l := by
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
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux03_12 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux03_14 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux03_21 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux03_24 a ha
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
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux03_41 a ha
  · exact star1to4_star4to1_self_aux03_42 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide

end TernaryPeriodPolynomials.Argument.Coercivity
