module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorArithmetic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem generalLinearGroup_scalar_commute {R : Type*} [CommRing R] {dimension : Type*}
    [Fintype dimension] [DecidableEq dimension] (unit : Rˣ) (matrix : GeneralLinearGroup dimension R) :
    Commute (GeneralLinearGroup.scalar dimension unit) matrix := by
  apply Units.ext
  change (GeneralLinearGroup.scalar dimension unit).val * matrix.val =
    matrix.val * (GeneralLinearGroup.scalar dimension unit).val
  rw [GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute unit.val (fun _ => Commute.all _ _) matrix.val).eq

theorem cuspidalTensorFiniteLevel_centralIntegralReal {V : Type} [AddCommGroup V] [Module ℂ V]
    (cusp : CuspidalRepresentation) (values : cuspidalTensorValues cusp V)
    (fixed : values ∈ cuspidalTensorFiniteLevel cusp V) (unit : ℤˣ) (argument : BinaryAdelicGL) :
    values.val (argument * atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) (GeneralLinearGroup.scalar (Fin 2) unit))) =
      values.val argument := by
  let matrix := GeneralLinearGroup.scalar (Fin 2) unit
  have commutes : Commute
      (GeneralLinearGroup.map rationalAdele (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix)) argument := by
    dsimp only [matrix]
    rw [GeneralLinearGroup.map_scalar, GeneralLinearGroup.map_scalar]
    exact generalLinearGroup_scalar_commute _ argument
  have invariant := cuspidalTensorValues_leftRational cusp values (GeneralLinearGroup.map (Int.castRingHom ℚ) matrix) argument
  rw [commutes.eq, binaryRationalMatrix_split, binaryIntegral_rational_real, binaryIntegral_rational_finite,
    ← mul_assoc, fixed] at invariant
  exact invariant

end TernaryPeriodPolynomials.SphericalDetection.Helpers
