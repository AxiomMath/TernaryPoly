module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneFiniteLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarModularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cuspidalTensorValues_leftRational (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp V) (matrix : BinaryRationalGL) (argument : BinaryAdelicGL) :
    values.val (GeneralLinearGroup.map rationalAdele matrix * argument) = values.val argument := by
  apply (Module.Free.chooseBasis ℂ V).eval_injective
  apply LinearMap.ext
  intro functional
  change functional (values.val (GeneralLinearGroup.map rationalAdele matrix * argument)) = functional (values.val argument)
  have invariant := cusp.leftRational matrix (cuspidalTensorFunctional cusp functional values) argument
  simpa only [cuspidalTensorFunctional_realize] using invariant

theorem binaryIntegral_rational_finite (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) =
      GeneralLinearGroup.map integralEmbedding (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) matrix) := by
  apply Units.ext
  funext row column
  simp [GeneralLinearGroup.map_apply]

theorem binaryIntegral_rational_real (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) =
      GeneralLinearGroup.map (Int.castRingHom ℝ) matrix := by
  apply Units.ext
  funext row column
  simp [GeneralLinearGroup.map_apply]

theorem cuspidalTensorFiniteLevel_integralReal (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp V) (fixed : values ∈ cuspidalTensorFiniteLevel cusp V)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    values.val (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix)) = values.val 1 := by
  have invariant := cuspidalTensorValues_leftRational cusp values
    (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) 1
  rw [mul_one, binaryRationalMatrix_split, binaryIntegral_rational_real, binaryIntegral_rational_finite,
    fixed] at invariant
  exact invariant

theorem normPower_binaryIntegralReal (matrix : GeneralLinearGroup (Fin 2) ℤ) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix))) exponent = 1 := by
  rw [binary_det_atInfinity, normPower, adeleNorm_realAdeleUnit, binary_det_map]
  rcases Int.units_eq_one_or (GeneralLinearGroup.det matrix) with determinant | determinant <;>
    simp [determinant]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
