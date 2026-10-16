module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalProjectedValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realRadicalInverseLevi (matrix : BinaryRealGL) : RealPlaneRadical →* RealPlaneRadical :=
  (realPlaneRadicalAction matrix⁻¹).toMonoidHom

theorem realRadicalInverseLevi_product (matrix : BinaryRealGL) (element : RealPlaneRadical) :
    (SemidirectProduct.inl element : RealPlaneGroup) * SemidirectProduct.inr matrix =
      SemidirectProduct.inr matrix * SemidirectProduct.inl (realRadicalInverseLevi matrix element) := by
  have conjugation := SemidirectProduct.inl_aut (φ := realPlaneRadicalAction) matrix⁻¹ element
  change SemidirectProduct.inl (realRadicalInverseLevi matrix element) = _ at conjugation
  rw [conjugation, inv_inv, map_inv, ← mul_assoc, mul_inv_cancel_left]

theorem realUpperCuspidalRep_inl (degree : ℕ) (cusp : CuspidalRepresentation) (element : RealPlaneRadical) :
    (realUpperCuspidalRep degree cusp).ρ element =
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl element) := by
  apply LinearMap.ext
  intro values
  exact (realPlaneCuspidalRep_radical degree cusp element values).symm

def realUpperCuspidalLevi (degree : ℕ) (cusp : CuspidalRepresentation) (matrix : BinaryRealGL) :
    Module.End ℂ (realUpperCuspidalRep degree cusp) :=
  (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inr matrix)

theorem realUpperCuspidalLevi_intertwines (degree : ℕ) (cusp : CuspidalRepresentation) (matrix : BinaryRealGL)
    (element : RealPlaneRadical) :
    ((realUpperCuspidalRep degree cusp).ρ element).comp (realUpperCuspidalLevi degree cusp matrix) =
      (realUpperCuspidalLevi degree cusp matrix).comp
        ((realUpperCuspidalRep degree cusp).ρ (realRadicalInverseLevi matrix element)) := by
  rw [realUpperCuspidalRep_inl, realUpperCuspidalRep_inl]
  change (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl element) *
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inr matrix) =
    (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inr matrix) *
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl (realRadicalInverseLevi matrix element))
  rw [← map_mul, ← map_mul, realRadicalInverseLevi_product]

def realUpperCuspidalCocycleLevi (degree : ℕ) (cusp : CuspidalRepresentation) (matrix : BinaryRealGL) :
    Module.End ℂ (groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) :=
  oneCocyclePullback _ _ (realRadicalInverseLevi matrix) (realUpperCuspidalLevi degree cusp matrix)
    (realUpperCuspidalLevi_intertwines degree cusp matrix)

theorem realUpperCuspidalCocycleLevi_apply (degree : ℕ) (cusp : CuspidalRepresentation) (matrix : BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) (element : RealPlaneRadical)
    (argument : BinaryAdelicGL) :
    (realUpperCuspidalCocycleLevi degree cusp matrix cycle element).val argument =
      normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
        realCoefficientComponent degree trivialCharacter (planeLevi matrix 1)
          ((cycle (realRadicalInverseLevi matrix element)).val (argument * atInfinity matrix)) := by
  change ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inr matrix)
    (cycle (realRadicalInverseLevi matrix element))).val argument = _
  have equality := realPlaneCuspidalRep_apply degree cusp trivialCharacter
    (SemidirectProduct.inr matrix)
    (cycle (realRadicalInverseLevi matrix element)) argument
  rw [realPlaneMatrix_inr] at equality
  exact equality

theorem realRadicalInverseLevi_axis (matrix : BinaryRealGL) (coordinate index : Fin 2) :
    (realRadicalInverseLevi matrix (realRadicalAxis coordinate 1)).toAdd index = matrix⁻¹.val index coordinate := by
  change (realPlaneRadicalAction matrix⁻¹ (realRadicalAxis coordinate 1)).toAdd index = _
  rw [realPlaneRadicalAction_apply]
  fin_cases coordinate <;> fin_cases index <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, realRadicalAxis]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
