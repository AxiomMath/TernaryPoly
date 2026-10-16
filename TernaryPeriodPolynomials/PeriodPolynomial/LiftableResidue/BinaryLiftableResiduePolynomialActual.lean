module

public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResidueDetectionActual
public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResiduePolynomial

@[expose] public section

noncomputable section
namespace TernaryPoly.BinaryLiftableResiduePolynomial
open BinaryLiftableResidueDetection OrdinaryFullCoefficient

/-- Every actual single-pole Hom has zero actual residue in odd degree. -/
theorem residueHom_eq_zero_actual (n : ℕ) (hn : Odd n)
    (F : SinglePoleHom n (-1)) : residueHom n (-1) F=0 :=
  residueHom_eq_zero n hn (actualIntertwining (n+1) (successor_even hn)) F

/-- Every value of an actual single-pole Hom is a homogeneous polynomial in odd degree. -/
theorem value_polynomial_actual (n : ℕ) (hn : Odd n)
    (F : SinglePoleHom n (-1)) (c : OrdinaryIncidenceChains.Cycles) :
    ∃ p : SinglePole.V n,F.val c=SinglePole.polynomialInclusion n p :=
  value_polynomial n hn (actualIntertwining (n+1) (successor_even hn)) F c

/-- The actual reference coefficient is a literal homogeneous polynomial in odd degree. -/
theorem reference_polynomial_actual (n : ℕ) (hn : Odd n)
    (F : SinglePoleHom n (-1)) :
    ∃ p : SinglePole.V n,
      reference (SinglePole.singlePoleAction n (-1)) F=SinglePole.polynomialInclusion n p :=
  reference_polynomial n hn (actualIntertwining (n+1) (successor_even hn)) F

/-- The actual ordinary apartment equations force a homogeneous polynomial in odd degree. -/
theorem relations_polynomial_actual (n : ℕ) (hn : Odd n)
    (x : SinglePole.singlePole n) (hx : Relations (SinglePole.singlePoleAction n (-1)) x) :
    ∃ p : SinglePole.V n,x=SinglePole.polynomialInclusion n p :=
  relations_polynomial n hn (actualIntertwining (n+1) (successor_even hn)) x hx

end TernaryPoly.BinaryLiftableResiduePolynomial
