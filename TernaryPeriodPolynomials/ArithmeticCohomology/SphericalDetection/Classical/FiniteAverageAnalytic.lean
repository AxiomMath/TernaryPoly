module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FiniteDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.DimensionalEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspClassicalFiniteAverageFamily (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) :
    cuspClassicalVectors cusp halfWeight →L[ℂ] cuspClassicalVectors cusp halfWeight := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  exact if convergent : 3 < exponent.re then LinearMap.toContinuousLinearMap
    (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent) else 0

theorem cuspClassicalFiniteAverageFamily_apply (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent vector =
      cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent vector := by
  simp only [cuspClassicalFiniteAverageFamily, dite_eq_left convergent, LinearMap.coe_toContinuousLinearMap']

def cuspClassicalOperatorEvaluation (cusp : CuspidalRepresentation) (halfWeight : ℤ) :
    (cuspClassicalVectors cusp halfWeight →L[ℂ] cuspClassicalVectors cusp halfWeight) →ₗ[ℂ]
      ((cuspClassicalVectors cusp halfWeight) × BinaryRealGL → ℂ) where
  toFun operator pair := cuspClassicalRealization cusp halfWeight (operator pair.1) pair.2
  map_add' first second := by ext pair; simp
  map_smul' scalar operator := by ext pair; simp

theorem cuspClassicalOperatorEvaluation_injective (cusp : CuspidalRepresentation) (halfWeight : ℤ) :
    Function.Injective (cuspClassicalOperatorEvaluation cusp halfWeight) := by
  intro first second equal
  apply ContinuousLinearMap.ext
  intro vector
  apply cuspClassicalRealization_injective cusp halfWeight
  funext real
  exact congrFun equal (vector, real)

theorem cuspClassicalFiniteAverageFamily_analyticAt (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re) :
    AnalyticAt ℂ (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative) exponent := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  apply analyticAt_of_separating_evaluations (cuspClassicalOperatorEvaluation cusp halfWeight)
    (cuspClassicalOperatorEvaluation_injective cusp halfWeight)
  rintro ⟨vector, real⟩
  have analytic := goodLineFinitePadicIntegral_analyticAt cusp (cuspSmoothAction cusp (atInfinity real) vector.val)
    (cuspSmoothAction_real_spherical cusp vector.val vector.property.1 real) exponent convergent
  apply analytic.congr
  have nearby : ∀ᶠ parameter : ℂ in nhds exponent, 3 < parameter.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds convergent
  filter_upwards [nearby] with parameter in_region
  change _ = cuspClassicalRealization cusp halfWeight
    (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative parameter vector) real
  rw [cuspClassicalFiniteAverageFamily_apply cusp central_positive halfWeight negative parameter in_region,
    cuspClassicalFiniteAverageOperator_realization]
  rfl

theorem cuspClassicalFiniteAverageFamily_endpoint_isUnit (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ) (negative : halfWeight < 0)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re) :
    IsUnit (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
      ((degree : ℂ) / 2 + 3 + cohomologicalPoint)) := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have equality : (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
      ((degree : ℂ) / 2 + 3 + cohomologicalPoint) : _ → _) =
      cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint) convergent := by
    funext vector
    exact cuspClassicalFiniteAverageFamily_apply cusp central_positive halfWeight negative _ convergent vector
  rw [equality]
  have injective := cuspClassicalFiniteAverageOperator_endpoint_injective cusp central_positive spherical_cusp large
    cohomological halfWeight negative weight convergent
  exact ⟨injective, LinearMap.injective_iff_surjective.mp injective⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
