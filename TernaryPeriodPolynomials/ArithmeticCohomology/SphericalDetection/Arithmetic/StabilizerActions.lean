module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerSplitting
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.H1Levi

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem identityPlaneSemidirectEquiv_apply
    (element : RadicalLattice ⋊[identityPlaneSplitting.conjAct] GeneralLinearGroup (Fin 2) ℤ) :
    (identityPlaneSemidirectEquiv element).val =
      upperRadicalLattice element.left * arithmeticLevi element.right := rfl

theorem goodLineSemidirectEquiv_apply
    (element : RadicalLattice ⋊[goodLineSplitting.conjAct] GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineSemidirectEquiv element).val =
      lowerRadicalLattice element.left * arithmeticLevi element.right := rfl

theorem arithmeticLevi_inv (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    arithmeticLevi matrix⁻¹ = (arithmeticLevi matrix)⁻¹ := arithmeticLeviHom.map_inv matrix

theorem identityPlaneSplitting_inverse_action (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (element : RadicalLattice) :
    identityPlaneSplitting.conjAct matrix⁻¹ element = upperLeviLatticeInput matrix element := by
  apply upperRadicalLattice_injective
  have equality := identityPlaneExtension.inl_conjAct_comm
    (e := identityPlaneLeviSection matrix⁻¹) (n := element)
  have mapped := congrArg Subtype.val equality
  change upperRadicalLattice (identityPlaneSplitting.conjAct matrix⁻¹ element) =
    arithmeticLevi matrix⁻¹ * upperRadicalLattice element * (arithmeticLevi matrix⁻¹)⁻¹ at mapped
  rw [arithmeticLevi_inv, inv_inv, mul_assoc, upperLeviLatticeInput_conjugation, inv_mul_cancel_left] at mapped
  exact mapped

theorem goodLineSplitting_inverse_action (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (element : RadicalLattice) :
    goodLineSplitting.conjAct matrix⁻¹ element = lowerLeviLatticeInput matrix element := by
  apply lowerRadicalLattice_injective
  have equality := goodLineExtension.inl_conjAct_comm
    (e := goodLineLeviSection matrix⁻¹) (n := element)
  have mapped := congrArg Subtype.val equality
  change lowerRadicalLattice (goodLineSplitting.conjAct matrix⁻¹ element) =
    arithmeticLevi matrix⁻¹ * lowerRadicalLattice element * (arithmeticLevi matrix⁻¹)⁻¹ at mapped
  rw [arithmeticLevi_inv, inv_inv, mul_assoc, lowerLeviLatticeInput_conjugation, inv_mul_cancel_left] at mapped
  exact mapped

def identityPlaneCoefficientRep (degree : ℕ) :
    Rep ℂ (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))) :=
  Rep.of ((rationalCoefficientComponent degree trivialCharacter).comp
    (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))).subtype)

def goodLineCoefficientRep (degree : ℕ) :
    Rep ℂ (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :=
  Rep.of ((rationalCoefficientComponent degree trivialCharacter).comp
    (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)).subtype)

theorem identityPlaneCoefficientRep_radical (degree : ℕ) :
    Rep.res identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) = upperRadicalLatticeRep degree := rfl

theorem goodLineCoefficientRep_radical (degree : ℕ) :
    Rep.res goodLineRadicalInclusion (goodLineCoefficientRep degree) = lowerRadicalLatticeRep degree := rfl

theorem identityPlaneCoefficientRep_section (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (identityPlaneCoefficientRep degree).ρ (identityPlaneLeviSection matrix) = arithmeticLeviCoefficient degree matrix := rfl

theorem goodLineCoefficientRep_section (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineCoefficientRep degree).ρ (goodLineLeviSection matrix) = arithmeticLeviCoefficient degree matrix := rfl

theorem identityPlaneSplitting_cocycle_action (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (upperRadicalLatticeRep degree)) (element : RadicalLattice) :
    upperRadicalCocycleLevi degree matrix cycle element =
      (identityPlaneCoefficientRep degree).ρ (identityPlaneLeviSection matrix)
        (cycle (identityPlaneSplitting.conjAct matrix⁻¹ element)) := by
  rw [identityPlaneCoefficientRep_section, identityPlaneSplitting_inverse_action, upperRadicalCocycleLevi_apply]
  rfl

theorem goodLineSplitting_cocycle_action (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep degree)) (element : RadicalLattice) :
    lowerRadicalCocycleLevi degree matrix cycle element =
      (goodLineCoefficientRep degree).ρ (goodLineLeviSection matrix)
        (cycle (goodLineSplitting.conjAct matrix⁻¹ element)) := by
  rw [goodLineCoefficientRep_section, goodLineSplitting_inverse_action, lowerRadicalCocycleLevi_apply]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
