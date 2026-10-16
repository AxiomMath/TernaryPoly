module

public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResiduePolynomial
public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.ResidueExtreme
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.CoefficientSymmetry

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryLiftableResiduePolynomial
open BinaryLiftableResidueDetection OrdinaryFullCoefficient SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower SinglePoleSupport

variable {n k : ℕ}

/-- The actual rational trace satisfies the actual ordinary apartment equations, with the entire
zero-scalar tower decomposition retained as explicit input. -/
theorem homogeneousTrace_relations (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    Relations (SinglePole.singlePoleAction n (-1)) (homogeneousTrace f hf q hq hd) := by
  apply singlePole_relations_of_symmetry n _
  · exact homogeneousTrace_permutation f hf q hq hd hr.1 hs (-1)
  · intro s
    have h := homogeneousTrace_sign f hf q hq hd hr.1 hs (-1) s
    rwa [odd_scalar_neg_one,one_smul] at h
  · exact homogeneousTrace_norm f hf q hq hd l hl he hr hs (-1)

/-- The actual homogeneous rational trace is polynomial, conditional on the exact analytic
intertwining and the full supplied zero-scalar tower data. -/
theorem homogeneousTrace_polynomial (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    ∃ p : SinglePole.V n,homogeneousTrace f hf q hq hd=SinglePole.polynomialInclusion n p :=
  relations_polynomial n hn h _ (homogeneousTrace_relations f hf q hq hd l hl he hr hs)

/-- The same conclusion in the literal fraction field, with an actual degree-n polynomial witness. -/
theorem trace_polynomial (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    ∃ p : TP,p.IsHomogeneous n ∧ trace f q hq=SinglePole.embed p := by
  obtain ⟨p,hp⟩ := homogeneousTrace_polynomial hn h f hf q hq hd l hl he hr hs
  refine ⟨p.val,p.property,?_⟩
  simpa only [homogeneousTrace_val,SinglePole.polynomialInclusion_val] using congrArg Subtype.val hp

/-- The actual lowest period in the supplied zero-scalar tower vanishes; no tower decomposition
or scalar vanishing is inferred without its explicit hypotheses. -/
theorem lowest_eq_zero (hn : Odd n)
    (h : BinaryCuspPeriodDetection.ActualIntertwining (n+1) (successor_even hn))
    (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) : lowest q=0 := by
  obtain ⟨p,hp⟩ := homogeneousTrace_polynomial hn h f hf q hq hd l hl he hr hs
  have hz := coordinateResidue_homogeneousTrace f hf q hq hd 0
  rw [hp,SinglePoleCoordinate.coordinateResidue_polynomial] at hz
  have hb : lowestHomogeneous q hd=0 :=
    (smul_eq_zero.mp hz.symm).resolve_left (by norm_num)
  exact congrArg Subtype.val hb

end TernaryPoly.BinaryLiftableResiduePolynomial
