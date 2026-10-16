module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicCentralTrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.ClassicalEulerScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicEulerFactor_classical (cusp : CuspidalRepresentation) (place : FinitePlace)
    (central : cuspLocalPadicCentralChar cusp place = 1) (halfWeight : ℤ) (trace exponent : ℂ) :
    cuspLocalPadicEulerFactor cusp place
        (((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) ^ (halfWeight + 1) * trace) exponent =
      classicalPrimeEulerPolynomial (Rat.HeightOneSpectrum.primesEquiv place).val (-2 * halfWeight) trace
          (exponent - halfWeight - 2 + 1) /
        classicalPrimeEulerPolynomial (Rat.HeightOneSpectrum.primesEquiv place).val (-2 * halfWeight) trace
          (exponent - halfWeight - 2) := by
  rw [cuspLocalPadicEulerFactor, central,
    padicPrimeEulerNumerator_shift _ (Rat.HeightOneSpectrum.primesEquiv place).property.pos]
  simp only [mul_one]
  rw [padicClassicalEuler_polynomial_scaling _ (Rat.HeightOneSpectrum.primesEquiv place).property.pos,
    padicClassicalEuler_polynomial_scaling _ (Rat.HeightOneSpectrum.primesEquiv place).property.pos]
  congr 2
  ring

theorem cohomological_classicalEuler_argument {degree : ℕ} (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3)) :
    ((degree : ℂ) / 2 + 3 + cohomologicalPoint) - halfWeight - 2 = (degree : ℂ) + 1 := by
  have equality : (2 : ℂ) * halfWeight = -((degree : ℂ) + 3) := by exact_mod_cast weight
  unfold cohomologicalPoint
  linear_combination -(1 / 2 : ℂ) * equality

theorem cuspLocalPadicEulerFactor_cohomological (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree)
    (place : FinitePlace) (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3)) (trace : ℂ) :
    cuspLocalPadicEulerFactor cusp place
        (((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) ^ (halfWeight + 1) * trace)
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint) =
      classicalPrimeEulerPolynomial (Rat.HeightOneSpectrum.primesEquiv place).val ((degree : ℤ) + 3) trace
          ((degree : ℂ) + 2) /
        classicalPrimeEulerPolynomial (Rat.HeightOneSpectrum.primesEquiv place).val ((degree : ℤ) + 3) trace
          ((degree : ℂ) + 1) := by
  have weight_eq : -2 * halfWeight = (degree : ℤ) + 3 := by omega
  rw [cuspLocalPadicEulerFactor_classical cusp place
    (cohomological_cuspLocalPadicCentralChar_eq_one cusp spherical cohomological place),
    cohomological_classicalEuler_argument halfWeight weight, weight_eq]
  congr 2
  ring

theorem cohomological_localExponent_convergent {degree : ℕ} (large : 1 < degree) :
    2 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re := by
  have large_real : (1 : ℝ) < degree := by exact_mod_cast large
  norm_num [cohomologicalPoint, Complex.add_re, Complex.div_re]
  linarith

end TernaryPeriodPolynomials.SphericalDetection.Helpers
