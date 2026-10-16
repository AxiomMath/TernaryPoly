module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.IntegralReductionLift
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.LowestFormDetection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryIntegerGL_adelic_factor (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map rationalAdele (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) =
      atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) *
        atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) matrix) := by
  rw [binaryIntegerGL_map_map]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, atFinite, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.map] <;> rfl

theorem cusp_realize_integerGL_translation (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (integralMatrix : GeneralLinearGroup (Fin 2) ℤ)
    (fixed : cuspSmoothAction cusp
      (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) integralMatrix)) vector = vector)
    (matrix : BinaryRealGL) :
    cusp.realize vector (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix) * atInfinity matrix) =
      cusp.realize vector (atInfinity matrix) := by
  have finite_identity (argument : BinaryAdelicGL) :=
    cusp.equivariant (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) integralMatrix)) vector argument
  change ∀ argument, cusp.realize
    (cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) integralMatrix)) vector)
      argument = _ at finite_identity
  simp only [fixed] at finite_identity
  calc
    _ = cusp.realize vector
      ((atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix) * atInfinity matrix) *
        atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) integralMatrix)) := finite_identity _
    _ = cusp.realize vector
      (GeneralLinearGroup.map rationalAdele (GeneralLinearGroup.map (Int.castRingHom ℚ) integralMatrix) *
        atInfinity matrix) := by
      rw [binaryIntegerGL_adelic_factor, mul_assoc, binary_atInfinity_atFinite_commute matrix, ← mul_assoc]
    _ = _ := cusp.leftRational _ vector _

theorem cusp_realize_integerGL_finite_translate (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (integralMatrix : GeneralLinearGroup (Fin 2) ℤ) (matrix : BinaryRealGL) :
    cusp.realize (cuspSmoothAction cusp
      (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) integralMatrix)) vector) (atInfinity matrix) =
    cusp.realize vector (atInfinity ((GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix)⁻¹ * matrix)) := by
  change cusp.realize ⟨_, _⟩ _ = _
  rw [cusp.equivariant]
  have identity : atInfinity matrix * atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) integralMatrix) =
      GeneralLinearGroup.map rationalAdele (GeneralLinearGroup.map (Int.castRingHom ℚ) integralMatrix) *
        atInfinity ((GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix)⁻¹ * matrix) := by
    rw [binaryIntegerGL_adelic_factor, mul_assoc, ← binary_atInfinity_atFinite_commute,
      ← mul_assoc, ← binary_atInfinity_mul, mul_inv_cancel_left]
  rw [identity, cusp.leftRational]

theorem cohomological_realize_zero_all_real_of_reflection_fixed
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (zero : cuspUpperHalfForm cusp weight vector 1 = 0)
    (fixed : cuspSmoothAction cusp
      (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) binaryIntegralRowReflection)) vector = vector)
    (matrix : BinaryRealGL) : cusp.realize vector (atInfinity matrix) = 0 := by
  by_cases positive : 0 < (GeneralLinearGroup.det matrix : ℝ)
  · exact cohomological_realize_zero_of_upperHalfForm_zero cohomological weight vector rotation zero matrix positive
  · have negative : (GeneralLinearGroup.det matrix : ℝ) < 0 :=
      lt_of_le_of_ne (le_of_not_gt positive) (Units.ne_zero _)
    have reflected_positive : 0 < ((GeneralLinearGroup.det
        (GeneralLinearGroup.map (Int.castRingHom ℝ) binaryIntegralRowReflection * matrix)) : ℝ) := by
      rw [map_mul, Units.val_mul, binaryIntegralRowReflection_real_det]
      linarith
    have reflected_zero := cohomological_realize_zero_of_upperHalfForm_zero cohomological weight vector rotation zero
      (GeneralLinearGroup.map (Int.castRingHom ℝ) binaryIntegralRowReflection * matrix) reflected_positive
    rw [binary_atInfinity_mul, cusp_realize_integerGL_translation cusp vector binaryIntegralRowReflection fixed matrix]
      at reflected_zero
    exact reflected_zero

theorem cuspPrincipalLowest_zero_of_real_slice
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (weight_positive : 0 < weight) (vector : cuspPrincipalLowestSubmodule cusp weight)
    (zero : ∀ matrix : BinaryRealGL, cusp.realize vector.val (atInfinity matrix) = 0) : vector = 0 := by
  apply cuspPrincipalLowestForm_integral_detection cohomological weight weight_positive vector
  intro matrix
  obtain ⟨integralMatrix, same⟩ := binaryIntegral_integer_representative matrix
  rw [← cuspPrincipalLowestIntegralAction_same_reduction cusp weight _ matrix same]
  have translated_zero (realMatrix : BinaryRealGL) : cusp.realize
      (cuspPrincipalLowestIntegralAction cusp weight
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix) vector).val (atInfinity realMatrix) = 0 := by
    change cusp.realize (cuspSmoothAction cusp (atFinite
      (GeneralLinearGroup.map integralEmbedding (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix)))
        vector.val) (atInfinity realMatrix) = 0
    rw [binaryIntegerGL_map_map, cusp_realize_integerGL_finite_translate, zero]
  apply DFunLike.ext
  intro point
  simp only [cuspPrincipalLowestForm_apply, cuspUpperHalfForm, cuspHolomorphicFunction,
    cuspUpperHalfOrbit_apply, one_mul, translated_zero, smul_zero, _root_.zero_apply]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
