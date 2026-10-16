module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneNaturalityAlgebra
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalBinaryTransvections
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalKernelDescent

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice RadicalFirstCohomology
open LatticeTopCohomology LatticeFirstCohomology groupCohomology RadicalTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The erased plane contraction intertwines the complete actual inverse-conjugation Levi action. -/
theorem planeCocycleContract_Levi (n : ℕ) (M : GL2) (c : cocycles₁ (planeRep n)) :
    (planeCocycleContract n
      (mapCocycles₁ (matrixLattice M⁻¹).toMonoidHom (planeCoefficientHom n M) c) :
        MvPolynomial (Fin 2) ℚ)=
      binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) M⁻¹).val
        (planeCocycleContract n c : MvPolynomial (Fin 2) ℚ) := by
  change X 0*(planeEval n (PolynomialGLAction.integralAction n 0 (planeElement M 0)
      (c (matrixLattice M⁻¹ first))) : MvPolynomial (Fin 2) ℚ)+
    X 1*(planeEval n (PolynomialGLAction.integralAction n 0 (planeElement M 0)
      (c (matrixLattice M⁻¹ second))) : MvPolynomial (Fin 2) ℚ)=_
  rw [planeEval_Levi,planeEval_Levi,planeEval_cocycle_matrix_first,planeEval_cocycle_matrix_second]
  exact binary_matrix_contraction M⁻¹ (planeEval n (c first)) (planeEval n (c second))

/-- Equality of genuine cohomology classes gives equality of their erased contractions. -/
theorem planeCocycleContract_eq_of_H1π_eq (n : ℕ) (c d : cocycles₁ (planeRep n))
    (h : H1π (planeRep n) c=H1π (planeRep n) d) :
    planeCocycleContract n c=planeCocycleContract n d := by
  exact linearMap_eq_of_kernel (H1π (planeRep n)).hom (planeCocycleContract n)
    (fun z hz => (planeCocycleContract_eq_zero_iff n z).mpr hz) c d h

/-- Opposite nonzero integral transvections kill every actual homogeneous plane-radical H¹ class. -/
theorem plane_lattice_transvectionSteps_fixed_zero (n : ℕ) (k l : ℤ)
    (hk : k≠0) (hl : l≠0) (x : groupCohomology (planeRep n) 1)
    (hu : planeH1Action n (binaryUpperStep k) x=x)
    (hv : planeH1Action n (binaryLowerStep l) x=x) : x=0 := by
  revert hu hv
  refine H1_induction_on x ?_
  intro c hu hv
  apply (planeCocycleContract_eq_zero_iff n c).mp
  apply binary_transvectionSteps_fixed_zero (Nat.succ_pos n) (k : ℚ) (l : ℚ)
    (by exact_mod_cast hk) (by exact_mod_cast hl)
  · have he := planeCocycleContract_eq_of_H1π_eq n _ c
      (by simpa only [planeH1Action,H1π_comp_map_apply] using hu)
    have hn := planeCocycleContract_Levi n (binaryUpperStep k) c
    rw [he,binaryUpperStep_substitute] at hn
    exact hn.symm
  · have he := planeCocycleContract_eq_of_H1π_eq n _ c
      (by simpa only [planeH1Action,H1π_comp_map_apply] using hv)
    have hn := planeCocycleContract_Levi n (binaryLowerStep l) c
    rw [he,binaryLowerStep_substitute] at hn
    exact hn.symm

/-- The actual derived step-three congruence transvections suffice in every coefficient degree. -/
theorem plane_lattice_stepThree_fixed_zero (n : ℕ) (x : groupCohomology (planeRep n) 1)
    (hu : planeH1Action n (binaryUpperStep 3) x=x)
    (hl : planeH1Action n (binaryLowerStep 3) x=x) : x=0 :=
  plane_lattice_transvectionSteps_fixed_zero n 3 3 (by norm_num) (by norm_num) x hu hl

end TernaryPoly.OrdinaryFaceRadical
