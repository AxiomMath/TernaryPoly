module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesA
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Eps5ValuesB

@[expose] public section



/-! R4, first index fixed to `1`. Unlike R1-R3, `β : OneCoordinates` carries no alternating
constraint, so no canonical-extension substitution is needed before the case split; this mirrors
the first-index-only split that worked for R2 (3 free indices total, 25 branches per file). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem hodgeStarRule_four_aux1 (β : OneCoordinates) (j k : Fin 5) :
    contractionFour (star1to4 β) 1 j k = -star2to3 (exteriorOne β) 1 j k := by
  fin_cases j <;> fin_cases k <;>
    simp [contractionFour, star1to4, star2to3, exteriorOne,
      Fin.sum_univ_five, map_add, Derivation.map_smul] <;>
    module

end TernaryPeriodPolynomials.Argument.Coercivity
