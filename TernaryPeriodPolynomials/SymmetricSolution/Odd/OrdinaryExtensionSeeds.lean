module

public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResiduePolynomialTraceActual
public import TernaryPeriodPolynomials.SymmetricSolution.Odd.SeedData

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly
open SymmetricOddRationalTower

/-- The original odd homogeneous symmetric Todd-zero hypotheses produce a genuine finite tower
whose actual lowest period vanishes. The tower is constructed rather than supplied as a premise. -/
theorem symmetric_odd_period_tower_lowest_zero {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ k : ℕ, ∃ q : Fin k → MvPolynomial (Fin 2) ℚ, ∃ l : Fin k → TernaryPolynomial,
      (∀ i,SymmetricBinaryPeriodRelations (q i) ∧
        (q i).IsHomogeneous (n+1-2*(i:ℕ)) ∧
        binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i) ∧
      f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i ∧ lowest q=0 := by
  obtain ⟨k,q,l,hq,he⟩ := symmetric_odd_period_tower hf hn hrel.1 hs hJ
  refine ⟨k,q,l,hq,he,?_⟩
  exact BinaryLiftableResiduePolynomial.lowest_eq_zero_actual hn f hf q
    (fun i => (hq i).1) (fun i => (hq i).2.1) l (fun i => (hq i).2.2) he hrel hs

/-- Every odd homogeneous symmetric period polynomial in the entire Todd kernel has full
polynomial seed data, including all signed, pure norm, and mixed substitution equations. -/
theorem symmetric_odd_polynomial_seeds {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hn : Odd n)
    (hrel : PeriodRelations f) (hs : S f=f) (hJ : symmetricTodd f=0) :
    ∃ P Q : TernaryPolynomial,SymmetricSeedData f P Q := by
  obtain ⟨k,q,l,hq,he,hzero⟩ := symmetric_odd_period_tower_lowest_zero hf hn hrel hs hJ
  refine ⟨regular q (X 0) (X 1) (X 2),qPolynomial q (fun i => (hq i).1),?_⟩
  rw [he]
  exact polynomial_data_of_lowest_zero q (fun i => (hq i).1) l
    (fun i => (hq i).2.2) hzero

end TernaryPoly
