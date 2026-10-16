module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBinaryRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorIntegralMap

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realUpperCuspidalBinarySection (degree : ℕ) (cusp : CuspidalRepresentation) :
    cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) →ₗ[ℂ]
      groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) where
  toFun values := ⟨fun element => cuspidalTensorMap cusp (realUpperBinaryValue degree element) values, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    apply Subtype.ext
    funext argument
    exact realUpperBinaryValue_mul degree first second (values.val argument)⟩
  map_add' first second := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_add (cuspidalTensorMap cusp (realUpperBinaryValue degree element)) first second
  map_smul' scalar values := by
    apply groupCohomology.cocycles₁_ext
    intro element
    exact map_smul (cuspidalTensorMap cusp (realUpperBinaryValue degree element)) scalar values

theorem realUpperCuspidalBinarySection_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (element : RealPlaneRadical) (argument : BinaryAdelicGL) :
    (realUpperCuspidalBinarySection degree cusp values element).val argument =
      realUpperBinarySection degree (values.val argument) element := rfl

theorem realUpperCuspidalBinarySection_coordinate (degree : ℕ) (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1))) :
    realUpperCuspidalBinaryCoordinate degree cusp (realUpperCuspidalBinarySection degree cusp values) = values := by
  apply Subtype.ext
  funext argument
  apply Subtype.ext
  rw [realUpperCuspidalBinaryCoordinate_value]
  have projected (coordinate : Fin 2) :
      binaryPolynomialRestrict
        ((realUpperCuspidalBinarySection degree cusp values (realRadicalAxis coordinate 1)).val argument).val =
      pderiv coordinate (values.val argument).val := by
    rw [realUpperCuspidalBinarySection_apply, realUpperBinarySection_restrict]
    fin_cases coordinate <;> simp [realRadicalAxis]
  rw [projected, projected]
  have euler := (values.val argument).property.sum_X_mul_pderiv
  rw [Fin.sum_univ_two, ← Nat.cast_smul_eq_nsmul ℂ] at euler
  rw [euler, smul_smul]
  have nonzero : ((degree + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero degree)
  simp only [← Nat.cast_add_one, inv_mul_cancel₀ nonzero, one_smul]

theorem realUpperCuspidalBinarySection_divided_boundary (degree : ℕ) (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (element : RealPlaneRadical) :
    realUpperCuspidalBinarySection degree cusp values element =
      -cuspidalTensorMap cusp (homogeneousLastDivide degree)
        (oneBoundaryCycle (realUpperCuspidalRep (degree + 1) cusp)
          (cuspidalTensorMap cusp (binaryHomogeneousLift (degree + 1)) values) element) := by
  apply Subtype.ext
  funext argument
  change homogeneousLastDivide degree
      (binaryHomogeneousLift (degree + 1) (values.val argument) -
        (realUpperRadicalRep (degree + 1)).ρ element (binaryHomogeneousLift (degree + 1) (values.val argument))) =
    -(homogeneousLastDivide degree
      ((realUpperRadicalRep (degree + 1)).ρ element (binaryHomogeneousLift (degree + 1) (values.val argument)) -
        binaryHomogeneousLift (degree + 1) (values.val argument)))
  rw [← map_neg, neg_sub]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
