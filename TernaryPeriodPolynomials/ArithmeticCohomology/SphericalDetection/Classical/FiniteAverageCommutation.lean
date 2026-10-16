module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FiniteAverage

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalTruncatedEulerEquiv_tendsto (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) :
    Tendsto (fun places => cuspClassicalTruncatedEulerEquiv cusp central_positive halfWeight negative
      exponent convergent places vector) atTop
        (nhds (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent vector)) := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  have embedding := (cuspClassicalRealization cusp halfWeight).isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (cuspClassicalRealization_injective cusp halfWeight))
  apply embedding.isEmbedding.tendsto_nhds_iff.mpr
  rw [cuspClassicalFiniteAverageOperator_realization]
  exact cuspClassicalTruncatedEulerEquiv_realization_tendsto cusp central_positive halfWeight negative
    exponent convergent vector

theorem cuspClassicalFiniteAverageOperator_hecke_commute (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent
        (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) =
      cuspClassicalPrimeHecke cusp central_positive halfWeight prime
        (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent vector) := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  have first := cuspClassicalTruncatedEulerEquiv_tendsto cusp central_positive halfWeight negative
    exponent convergent (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector)
  have second := ((cuspClassicalPrimeHecke cusp central_positive halfWeight prime).continuous_of_finiteDimensional.tendsto
    (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent vector)).comp
      (cuspClassicalTruncatedEulerEquiv_tendsto cusp central_positive halfWeight negative exponent convergent vector)
  simp_rw [cuspClassicalTruncatedEulerEquiv_hecke_commute] at first
  exact tendsto_nhds_unique first second

theorem cuspClassicalFiniteAverageOperator_ker_hecke (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight)
    (member : vector ∈ (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent).ker) :
    cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector ∈
      (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent).ker := by
  change cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent
    (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) = 0
  rw [cuspClassicalFiniteAverageOperator_hecke_commute, LinearMap.mem_ker.mp member, map_zero]

theorem cuspClassicalFiniteAverage_endpoint (degree : ℕ) (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (large : 3 < ((degree : ℂ) / 2 + 3 + cohomologicalPoint).re)
    (vector : cuspClassicalVectors cusp halfWeight) (real : BinaryRealGL) :
    cuspClassicalFiniteAverage cusp halfWeight ((degree : ℂ) / 2 + 3 + cohomologicalPoint) large vector real =
      goodLineFiniteVectorIntegral degree cusp cohomologicalPoint (cuspSmoothAction cusp (atInfinity real) vector.val) := by
  unfold cuspClassicalFiniteAverage goodLineFiniteVectorIntegral
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [goodLineFinitePadicIntegrand_eq degree cusp cohomologicalPoint _
    (cuspSmoothAction_real_spherical cusp vector.val vector.property.1 real)]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
