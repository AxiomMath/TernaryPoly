module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodInjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FiniteAverageAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalFiniteAverageFamily_period_zero_iff (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity.val)
    (exponent : ℂ) (convergent : 3 < exponent.re) (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity.val sign
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent vector) = 0 ↔
    cuspClassicalFiniteAverage cusp halfWeight exponent convergent vector = 0 := by
  have detects := cuspClassicalArithmeticPeriodMap_injective cusp central_positive halfWeight negative
    degree weight_eq even twist parity sign
  rw [cuspClassicalFiniteAverageFamily_apply cusp central_positive halfWeight negative exponent convergent]
  constructor
  · intro zero
    have vector_zero := detects (zero.trans (map_zero _).symm)
    rw [← cuspClassicalFiniteAverageOperator_realization cusp central_positive halfWeight negative
      exponent convergent, vector_zero, map_zero]
  · intro zero
    have vector_zero : cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative
        exponent convergent vector = 0 := by
      apply cuspClassicalRealization_injective cusp halfWeight
      rw [cuspClassicalFiniteAverageOperator_realization, zero, map_zero]
    rw [vector_zero, map_zero]

theorem goodLineFiniteVectorIntegral_zero_of_period_zero (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    {degree : ℕ} (large : 3 < degree) (odd : Odd degree)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : cuspClassicalVectors cusp halfWeight)
    (zero : cuspClassicalArithmeticPeriodMap cusp halfWeight (by omega) (degree + 1) (by omega)
      (by obtain ⟨half, equality⟩ := odd; exact ⟨half + 1, by omega⟩) 0 0 (by norm_num)
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight (by omega)
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint) vector) = 0) :
    ∀ real : BinaryRealGL, goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
      (cuspSmoothAction cusp (atInfinity real) vector.val) = 0 := by
  have convergent : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re := by
    have degree_large : (3 : ℝ) < degree := by exact_mod_cast large
    norm_num [cohomologicalPoint, Complex.add_re, Complex.div_re]
    linarith
  have vanishes := (cuspClassicalFiniteAverageFamily_period_zero_iff cusp central_positive halfWeight
    (by omega) (degree + 1) (by omega) (by obtain ⟨half, equality⟩ := odd; exact ⟨half + 1, by omega⟩)
    0 (0 : Fin 2) (by norm_num) _ convergent vector).mp zero
  intro real
  rw [← cuspClassicalFiniteAverage_endpoint degree cusp halfWeight convergent vector real]
  exact congrFun vanishes real

end TernaryPeriodPolynomials.SphericalDetection.Helpers
