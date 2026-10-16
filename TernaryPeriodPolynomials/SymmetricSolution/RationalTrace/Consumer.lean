module

public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.Decomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberMatrices

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower OrdinaryRationalFiber
open OrdinaryCovectors OrdinaryFiberPermutations OrdinarySignedFibers
open ReferenceCoefficientMatrices

variable {k : ℕ}

/-- The trace norm is the genuine reference-matrix norm on rational functions. -/
theorem trace_reference_norm (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (f : TP) (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hf : PeriodRelations f) (hs : S f=f) :
    trace f q hq+SinglePole.fractionEquiv (rational a) (trace f q hq)+
      SinglePole.fractionEquiv (rational a)
        (SinglePole.fractionEquiv (rational a) (trace f q hq))=0 := by
  rw [fractionEquiv_a_a,fractionEquiv_a]
  linear_combination trace_norm q hq l hl f he hf hs

/-- Actual finite rational extension and trace, with every correction term retained. -/
theorem rational_extension_and_trace (q : Fin k → BP)
    (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (f : TP) (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hf : PeriodRelations f) (hs : S f=f) :
    (∀ s π r,seedValue f q hq (permuteRow π (signRow s r))=
      (-1 : ℚ)^s.card • fracPerm π (fracSign s (seedValue f q hq r))) ∧
    (∀ r : Covector,r≠0 → fiberNorm (seedValue f q hq) r=0) ∧
    (∀ π,fracPerm π (trace f q hq)=trace f q hq) ∧
    (∀ i : Fin 3,fracSign {i} (trace f q hq)= -trace f q hq) ∧
    (trace f q hq+fracA (trace f q hq)+fracA2 (trace f q hq)=0) ∧
    (trace f q hq=2*OrdinaryResiduePolynomial.representative (lowest q) (X 0) (X 1) (X 2)+
      embed (polynomialCorrection f q hq)) :=
  ⟨seedValue_signed_permutation f q hq hf.1 hs,
    seedValue_all_norms q hq l hl f he hf hs,
    trace_permutation f q hq hf.1 hs,
    trace_separately_odd f q hq hf.1 hs,
    trace_norm q hq l hl f he hf hs,
    trace_residue_correction f q hq⟩

end TernaryPoly.SymmetricRationalTrace
