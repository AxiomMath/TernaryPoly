module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalBinaryTransvections
public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Naturality

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice SymmetricLineCohomology
open RelativeStabilizerMatrices

/-- Opposite nonzero integral transvections have no invariant actual line-radical H¹ classes. -/
theorem line_lattice_transvectionSteps_fixed_zero (n : ℕ) (k l : ℤ)
    (hk : k≠0) (hl : l≠0) (x : groupCohomology (lineRep n) 1)
    (hu : latticeH1LeviAction n 1 (binaryUpperStep k) x=x)
    (hv : latticeH1LeviAction n 1 (binaryLowerStep l) x=x) : x=0 := by
  apply (latticeH1ScalarEquiv n).injective
  rw [map_zero]
  apply binary_transvectionSteps_fixed_zero (Nat.succ_pos n) (k : ℚ) (l : ℚ)
    (by exact_mod_cast hk) (by exact_mod_cast hl)
  · have h := latticeH1ScalarEquiv_Levi n 1 (binaryUpperStep k) x
    rw [hu] at h
    simpa only [rationalBlock,binaryUpperStep_substitute] using h.symm
  · have h := latticeH1ScalarEquiv_Levi n 1 (binaryLowerStep l) x
    rw [hv] at h
    simpa only [rationalBlock,binaryLowerStep_substitute] using h.symm

/-- The step-three congruence transvections already kill every actual line H¹ invariant,
including the degree-zero coefficient case. -/
theorem line_lattice_stepThree_fixed_zero (n : ℕ) (x : groupCohomology (lineRep n) 1)
    (hu : latticeH1LeviAction n 1 (binaryUpperStep 3) x=x)
    (hl : latticeH1LeviAction n 1 (binaryLowerStep 3) x=x) : x=0 :=
  line_lattice_transvectionSteps_fixed_zero n 3 3 (by norm_num) (by norm_num) x hu hl

/-- The same vanishing holds on the actual integral radical subgroup with determinant twist. -/
theorem line_subgroup_stepThree_fixed_zero (n : ℕ)
    (x : groupCohomology (twistedSubgroupRep n) 1)
    (hu : subgroupH1LeviAction n 1 (binaryUpperStep 3) x=x)
    (hl : subgroupH1LeviAction n 1 (binaryLowerStep 3) x=x) : x=0 := by
  apply (subgroupH1ScalarEquiv n).injective
  rw [map_zero]
  apply binary_transvectionSteps_fixed_zero (Nat.succ_pos n) 3 3 (by norm_num) (by norm_num)
  · have h := subgroupH1ScalarEquiv_Levi n 1 (binaryUpperStep 3) x
    rw [hu] at h
    simpa only [rationalBlock,binaryUpperStep_substitute,Int.cast_ofNat] using h.symm
  · have h := subgroupH1ScalarEquiv_Levi n 1 (binaryLowerStep 3) x
    rw [hl] at h
    simpa only [rationalBlock,binaryLowerStep_substitute,Int.cast_ofNat] using h.symm

end TernaryPoly.OrdinaryFaceRadical
