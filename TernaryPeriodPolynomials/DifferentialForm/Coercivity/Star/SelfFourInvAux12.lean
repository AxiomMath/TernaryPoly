module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux12H03
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux12H04
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux12H30
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux12H34
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux12H40
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvAux12H43

@[expose] public section



/-! First-two-indices-`1,2` slice of the "down-then-up" involution
`star1to4 (star4to1 a) = (1/96) • a` for alternating `a : FourCoordinates`. The six genuinely
pairwise-distinct `(k, l)` branches (`k, l ∈ {0, 3, 4}`, `k ≠ l`) are each discharged by
their own lemma (imported above).



-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_star4to1_self_aux12 (a : FourCoordinates) (ha : IsAlternatingFour a)
    (k l : Fin 5) : star1to4 (star4to1 a) 1 2 k l = (1 / 96 : ℝ) • a 1 2 k l := by
  fin_cases k <;> fin_cases l
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux12_03 a ha
  · exact star1to4_star4to1_self_aux12_04 a ha
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
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux12_30 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux12_34 a ha
  · exact star1to4_star4to1_self_aux12_40 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · apply star1to4_star4to1_self_of_dup ha
    decide
  · exact star1to4_star4to1_self_aux12_43 a ha
  · apply star1to4_star4to1_self_of_dup ha
    decide

end TernaryPeriodPolynomials.Argument.Coercivity
