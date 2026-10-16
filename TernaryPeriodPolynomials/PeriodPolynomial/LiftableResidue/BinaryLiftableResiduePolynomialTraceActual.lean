module

public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResiduePolynomialActual
public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResiduePolynomialTrace

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryLiftableResiduePolynomial
open BinaryLiftableResidueDetection SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower

variable {n k : ℕ}

/-- The actual rational trace is a homogeneous polynomial, with the complete supplied tower retained. -/
theorem homogeneousTrace_polynomial_actual (hn : Odd n)
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    ∃ p : SinglePole.V n,homogeneousTrace f hf q hq hd=SinglePole.polynomialInclusion n p :=
  homogeneousTrace_polynomial hn (actualIntertwining (n+1) (successor_even hn)) f hf q hq hd l hl he hr hs

/-- The actual trace equals a homogeneous polynomial in the literal fraction field. -/
theorem trace_polynomial_actual (hn : Odd n)
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    ∃ p : TP,p.IsHomogeneous n ∧ trace f q hq=SinglePole.embed p :=
  trace_polynomial hn (actualIntertwining (n+1) (successor_even hn)) f hf q hq hd l hl he hr hs

/-- The actual lowest period vanishes for every supplied zero-scalar tower in odd degree. -/
theorem lowest_eq_zero_actual (hn : Odd n)
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) : lowest q=0 :=
  lowest_eq_zero hn (actualIntertwining (n+1) (successor_even hn)) f hf q hq hd l hl he hr hs

end TernaryPoly.BinaryLiftableResiduePolynomial
