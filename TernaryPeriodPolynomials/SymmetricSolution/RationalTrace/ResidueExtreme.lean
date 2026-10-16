module

public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.ResiduePolynomial
public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.SinglePoleActions
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.CanonicalOdd

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower SinglePoleCoordinate SinglePoleSupport

variable {n k : ℕ}

/-- The actual principal parts of the trace vanish away from the three coordinate axes. -/
theorem homogeneousTrace_residue_off_axes (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    ∀ H, ¬OrdinaryResidueSupport.Coordinate H →
      SinglePole.residue n (homogeneousTrace f hf q hq hd) H=0 :=
  singlePole_residue_coordinate_support n (-1) (homogeneousTrace f hf q hq hd)
    (homogeneousTrace_permutation f hf q hq hd hr.1 hs (-1))
    (homogeneousTrace_sign f hf q hq hd hr.1 hs (-1))
    (homogeneousTrace_norm f hf q hq hd l hl he hr hs (-1))

/-- Extreme coefficients vanish for the actual lowest tower period, identified through the literal
coordinate residue of the actual trace. This does not assert that the period itself vanishes. -/
theorem lowest_extreme_coefficients (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    ∀ m : Fin 1 →₀ ℕ,(lowest q).coeff (Finsupp.cons 1 m)=0 := by
  obtain ⟨v,p,_,hrep,_,hex⟩ := OrdinaryResidueGeneral.exists_period_lift_extreme n (-1)
    (homogeneousTrace f hf q hq hd)
    (homogeneousTrace_permutation f hf q hq hd hr.1 hs (-1))
    (homogeneousTrace_sign f hf q hq hd hr.1 hs (-1))
    (homogeneousTrace_norm f hf q hq hd l hl he hr hs (-1))
  have hv : v=(2 : ℚ) • lowestHomogeneous q hd :=
    (coordinateResidue_of_lift (homogeneousTrace f hf q hq hd) v p hrep 0).symm.trans
      (coordinateResidue_homogeneousTrace f hf q hq hd 0)
  have hv' : v.val=(2 : ℚ) • lowest q := congrArg Subtype.val hv
  intro m
  have hz := hex m
  rw [hv',coeff_smul] at hz
  change (2 : ℚ)*(lowest q).coeff (Finsupp.cons 1 m)=0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The actual homogeneous trace has exactly the three prescribed literal coordinate residues,
no other principal parts, and detects every extreme coefficient of its actual lowest period. -/
theorem actual_trace_residue_and_extreme (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) :
    (∀ i, coordinateResidue n i (homogeneousTrace f hf q hq hd)=
      (2 : ℚ) • lowestHomogeneous q hd) ∧
    (∀ H, ¬OrdinaryResidueSupport.Coordinate H →
      SinglePole.residue n (homogeneousTrace f hf q hq hd) H=0) ∧
    (∀ m : Fin 1 →₀ ℕ,(lowest q).coeff (Finsupp.cons 1 m)=0) :=
  ⟨coordinateResidue_homogeneousTrace f hf q hq hd,
    homogeneousTrace_residue_off_axes f hf q hq hd l hl he hr hs,
    lowest_extreme_coefficients f hf q hq hd l hl he hr hs⟩

end TernaryPoly.SymmetricRationalTrace
