module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspCentralCharacter_rational (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (unit : ℚˣ) : cusp.centralCharacter (Units.map rationalAdele unit) = 1 := by
  apply smul_left_injective ℂ nonzero
  dsimp only
  rw [one_smul, ← cuspSmoothAction_scalar]
  apply cusp.injective
  funext argument
  rw [cuspSmoothAction_realize, ← GeneralLinearGroup.scalar_commute, ← GeneralLinearGroup.map_scalar,
    cusp.leftRational]

theorem cuspCentralCharacter_finite_integral (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp) (unit : IntegralAdelesˣ) :
    cusp.centralCharacter (finiteAdeleUnit (Units.map integralEmbedding unit)) = 1 := by
  apply smul_left_injective ℂ nonzero
  dsimp only
  rw [one_smul, ← cuspSmoothAction_scalar, ← binary_atFinite_scalar, ← GeneralLinearGroup.map_scalar]
  exact cuspSmoothAction_finite_spherical cusp vector spherical _ ⟨GeneralLinearGroup.scalar (Fin 2) unit, rfl⟩

theorem rationalAdeleUnit_real_finite (unit : ℚˣ) :
    Units.map rationalAdele unit =
      realAdeleUnit (Units.map (algebraMap ℚ ℝ) unit) *
        finiteAdeleUnit (Units.map (algebraMap ℚ FiniteAdeles) unit) := by
  apply Units.ext
  apply Prod.ext <;> simp [realAdeleUnit, finiteAdeleUnit, rationalAdele]

theorem cuspCentralCharacter_finite_rational_positive (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (unit : ℚˣ) (positive : 0 < unit.val) :
    cusp.centralCharacter (finiteAdeleUnit (Units.map (algebraMap ℚ FiniteAdeles) unit)) = 1 := by
  have rational := cuspCentralCharacter_rational cusp vector nonzero unit
  rw [rationalAdeleUnit_real_finite, map_mul, central_positive _ (by
    change (0 : ℝ) < (unit.val : ℝ)
    exact_mod_cast positive), one_mul] at rational
  exact rational

end TernaryPeriodPolynomials.SphericalDetection.Helpers
