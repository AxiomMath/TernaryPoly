module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeFour

@[expose] public section



/-! The approximate inverse Hodge-star reindexing from four-forms to one-forms, mirroring
`star3to2`'s `1 / 3!`-normalized style (`HodgeStar.lean`) one degree further: `1 / 4!`. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

def star4to1 (c : FourCoordinates) : OneCoordinates := fun i =>
  (1 / 24 : ℝ) • ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
    (eps5 i j k l m * tangentWeight j * tangentWeight k * tangentWeight l * tangentWeight m) •
      c j k l m

end TernaryPeriodPolynomials.Argument.Coercivity
