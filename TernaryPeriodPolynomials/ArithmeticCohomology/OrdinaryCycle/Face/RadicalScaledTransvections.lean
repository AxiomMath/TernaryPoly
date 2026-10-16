module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalScalingCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalLineTransvections

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices PolynomialGLAction
open SymmetricLineCohomology RadicalTopCohomology RadicalFirstCohomology groupCohomology

/-- The coordinate-scaling H¹ isomorphism commutes with the actual plane Levi action. -/
theorem scaledPlaneH1Iso_natural (n : ℕ) (M : GL2)
    (x : groupCohomology (scaledPlaneRep n) 1) :
    (scaledPlaneH1Iso n).hom (scaledPlaneH1Action n M x)=
      planeH1Action n M ((scaledPlaneH1Iso n).hom x) := by
  refine H1_induction_on x ?_
  intro c
  simp only [scaledPlaneH1Iso,groupCohomology.mapIso,scaledPlaneH1Action,planeH1Action,
    H1π_comp_map_apply]
  apply congrArg (H1π (planeRep n))
  apply cocycles₁_ext
  intro g
  change homogeneousAction n 0 planeScale
      (homogeneousAction n 0 (GeneralLinearGroup.map (Int.castRingHom ℚ) (planeElement M 0))
        (c (matrixLattice M⁻¹ g)))=
    homogeneousAction n 0 (GeneralLinearGroup.map (Int.castRingHom ℚ) (planeElement M 0))
      (homogeneousAction n 0 planeScale (c (matrixLattice M⁻¹ g)))
  have he := congrArg (homogeneousAction n 0) (planeScale_Levi M)
  rw [map_mul,map_mul] at he
  exact LinearMap.congr_fun he _

/-- The coordinate-scaling H¹ isomorphism commutes with the full actual line Levi action. -/
theorem scaledLineH1Iso_natural (n : ℕ) (t : ℤˣ) (M : GL2)
    (x : groupCohomology (scaledLineRep n) 1) :
    (scaledLineH1Iso n).hom (scaledLineH1Action n t M x)=
      latticeH1LeviAction n t M ((scaledLineH1Iso n).hom x) := by
  refine H1_induction_on x ?_
  intro c
  simp only [scaledLineH1Iso,groupCohomology.mapIso,scaledLineH1Action,latticeH1LeviAction,
    H1π_comp_map_apply]
  apply congrArg (H1π (lineRep n))
  apply cocycles₁_ext
  intro g
  change homogeneousAction n (-1) lineScale
      (homogeneousAction n (-1) (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 M))
        (c (leviLatticeChange t M g)))=
    homogeneousAction n (-1) (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 M))
      (homogeneousAction n (-1) lineScale (c (leviLatticeChange t M g)))
  have he := congrArg (homogeneousAction n (-1)) (lineScale_Levi t M)
  rw [map_mul,map_mul] at he
  exact LinearMap.congr_fun he _

/-- The actual step-three plane lattice has no degree-one cohomology fixed by both derived steps. -/
theorem scaledPlaneH1_stepThree_fixed_zero (n : ℕ)
    (x : groupCohomology (scaledPlaneRep n) 1)
    (hu : scaledPlaneH1Action n (binaryUpperStep 3) x=x)
    (hl : scaledPlaneH1Action n (binaryLowerStep 3) x=x) : x=0 := by
  have hi : Function.Injective (scaledPlaneH1Iso n).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hi
  rw [map_zero]
  apply plane_lattice_stepThree_fixed_zero
  · rw [←scaledPlaneH1Iso_natural,hu]
  · rw [←scaledPlaneH1Iso_natural,hl]

/-- The actual step-three line lattice has no degree-one cohomology fixed by both derived steps. -/
theorem scaledLineH1_stepThree_fixed_zero (n : ℕ)
    (x : groupCohomology (scaledLineRep n) 1)
    (hu : scaledLineH1Action n 1 (binaryUpperStep 3) x=x)
    (hl : scaledLineH1Action n 1 (binaryLowerStep 3) x=x) : x=0 := by
  have hi : Function.Injective (scaledLineH1Iso n).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hi
  rw [map_zero]
  apply line_lattice_stepThree_fixed_zero
  · rw [←scaledLineH1Iso_natural,hu]
  · rw [←scaledLineH1Iso_natural,hl]

end TernaryPoly.OrdinaryFaceRadical
