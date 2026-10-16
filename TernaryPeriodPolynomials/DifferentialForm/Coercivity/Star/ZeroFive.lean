module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.OneFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.Algebra

@[expose] public section



/-! Degree-four-to-five extension completing the Hodge-star ladder at the top: `star0to5`/
`star5to0` (Λ⁰↔Λ⁵), `exteriorFour : FourCoordinates → Poly` (Λ⁴→Λ⁵, written as the explicit
five-term alternating sum, mirroring `exteriorThree`'s explicit four-term style rather than a
`Fin.succAbove`-indexed sum, since every term is a concrete numeral application), and
`contractionFive : Poly → FourCoordinates` (Λ⁵→Λ⁴, mirroring `contractionFour`'s one-extra-index
sum). Also `algebraicHodgeFour`, mirroring `algebraicHodgeOne`'s `d∘δ+δ∘d` shape one degree up. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity
open TernaryPeriodPolynomials.Argument.CoercivityOne

def star0to5 (p : Poly) : Poly := p

def star5to0 (q : Poly) : Poly := (∏ j : Fin 5, tangentWeight j) • q

def exteriorFour (a : FourCoordinates) : Poly :=
  infinitesimal (tangentFrame 0) (a 1 2 3 4) - infinitesimal (tangentFrame 1) (a 0 2 3 4) +
    infinitesimal (tangentFrame 2) (a 0 1 3 4) - infinitesimal (tangentFrame 3) (a 0 1 2 4) +
    infinitesimal (tangentFrame 4) (a 0 1 2 3)

def contractionFive (q : Poly) : FourCoordinates := fun i j k l =>
  ∑ m : Fin 5, (eps5 m i j k l * tangentWeight m) • infinitesimal (tangentFrame m) q

def algebraicHodgeFour (a : FourCoordinates) : FourCoordinates :=
  exteriorThree (contractionFour a) + contractionFive (exteriorFour a)

end TernaryPeriodPolynomials.Argument.Coercivity
