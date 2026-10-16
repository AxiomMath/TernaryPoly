module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalScalingMatrices
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalBinaryTransvections
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootModule

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices PolynomialGLAction
open SymmetricLineCohomology OrdinaryBoundaryCommonRoot OrdinaryCovectors ModThreeGoodAction

/-- A reduction-trivial matrix fixes every literal nonzero covector. -/
theorem rowMove_of_reduction_one (g : IntegralGL) (hg : reduction g=1) (r : NonzeroCovector) :
    rowMove g r=r := by
  apply Subtype.ext
  simp [rowMove,hg]

/-- Determinant-one matrices have the same literal coefficient action for all twists. -/
theorem integralAction_twist_eq_of_det_one (n : ℕ) (e f : ℤ) (g : IntegralGL)
    (hg : g.val.det=1) : integralAction n e g=integralAction n f g := by
  have hd : (GeneralLinearGroup.map (Int.castRingHom ℚ) g).val.det=1 := by
    calc
      _=(g.val.det : ℚ) := ((Int.castRingHom ℚ).map_det _).symm
      _=1 := by rw [hg]; rfl
  have he (k : ℤ) : determinantCharacter k (GeneralLinearGroup.map (Int.castRingHom ℚ) g)=1 := by
    change (GeneralLinearGroup.map (Int.castRingHom ℚ) g).val.det^k=1
    rw [hd,one_zpow]
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simp only [integralAction_coe,action_apply,he]

theorem planeHom_det (g : Lattice) : (planeHom g).val.det=1 := by
  simp [planeHom,planeElement_val,det_planeMatrix]

theorem planeHom_action_twist (n : ℕ) (e : ℤ) (g : Lattice) :
    integralAction n e (planeHom g)=(planeRep n).ρ g :=
  integralAction_twist_eq_of_det_one n e 0 (planeHom g) (planeHom_det g)

/-- The complete step-three plane radical fixes all twenty-six residue covectors. -/
theorem planeHom_scaled_reduction (g : Lattice) : reduction (planeHom (scaleLattice 3 g))=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reduction,GeneralLinearGroup.map_apply,planeHom,planeElement_val,planeMatrix,scaleLattice]
  all_goals exact Or.inl (by decide)

/-- The complete step-three line radical fixes all twenty-six residue covectors. -/
theorem lineHom_scaled_reduction (g : Lattice) : reduction (lineHom (scaleLattice 3 g))=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reduction,GeneralLinearGroup.map_apply,lineHom,lineElement_val,lineMatrix,scaleLattice]
  all_goals exact Or.inl (by decide)

theorem binaryUpperStep_det (k : ℤ) : (binaryUpperStep k).val.det=1 := by
  rw [Matrix.det_fin_two]
  simp [binaryUpperStep,binaryUpperMatrix]

theorem binaryLowerStep_det (k : ℤ) : (binaryLowerStep k).val.det=1 := by
  rw [Matrix.det_fin_two]
  simp [binaryLowerStep,binaryLowerMatrix]

theorem planeUpperStep_det (k : ℤ) : (planeElement (binaryUpperStep k) 0).val.det=1 := by
  simp [planeElement_val,det_planeMatrix,binaryUpperStep_det]

theorem planeLowerStep_det (k : ℤ) : (planeElement (binaryLowerStep k) 0).val.det=1 := by
  simp [planeElement_val,det_planeMatrix,binaryLowerStep_det]

theorem lineUpperStep_det (k : ℤ) : (lineElement 1 0 (binaryUpperStep k)).val.det=1 := by
  simp [lineElement_val,det_lineMatrix,binaryUpperStep_det]

theorem lineLowerStep_det (k : ℤ) : (lineElement 1 0 (binaryLowerStep k)).val.det=1 := by
  simp [lineElement_val,det_lineMatrix,binaryLowerStep_det]

theorem planeUpperThree_reduction : reduction (planeElement (binaryUpperStep 3) 0)=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reduction,GeneralLinearGroup.map_apply,planeElement_val,planeMatrix,binaryUpperStep,binaryUpperMatrix]
  decide

theorem planeLowerThree_reduction : reduction (planeElement (binaryLowerStep 3) 0)=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reduction,GeneralLinearGroup.map_apply,planeElement_val,planeMatrix,binaryLowerStep,binaryLowerMatrix]
  decide

theorem lineUpperThree_reduction : reduction (lineElement 1 0 (binaryUpperStep 3))=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reduction,GeneralLinearGroup.map_apply,lineElement_val,lineMatrix,binaryUpperStep,binaryUpperMatrix]
  decide

theorem lineLowerThree_reduction : reduction (lineElement 1 0 (binaryLowerStep 3))=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reduction,GeneralLinearGroup.map_apply,lineElement_val,lineMatrix,binaryLowerStep,binaryLowerMatrix]
  decide

end TernaryPoly.OrdinaryFaceRadical
