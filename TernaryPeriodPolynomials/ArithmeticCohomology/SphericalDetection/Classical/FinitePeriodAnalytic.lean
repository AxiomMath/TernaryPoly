module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FinitePeriodIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspClassicalArithmeticCocycleCoefficient (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    cuspClassicalVectors cusp halfWeight →ₗ[ℂ] ℂ :=
  let evaluation : groupCohomology.cocycles₁ (arithmeticBinaryRep degree twist) →ₗ[ℂ] ℂ :=
    { toFun := fun cycle => functional (cycle matrix)
      map_add' := fun first second => map_add functional (first matrix) (second matrix)
      map_smul' := fun scalar cycle => map_smul functional scalar (cycle matrix) }
  evaluation.comp ((classicalArithmeticCocycleMap (-2 * halfWeight) degree weight_eq even twist parity sign).comp
    (cuspClassicalFormMap cusp halfWeight negative))

theorem cuspClassicalArithmeticCocycleCoefficient_apply (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalArithmeticCocycleCoefficient cusp halfWeight negative degree weight_eq even twist parity sign
      matrix functional vector = functional (classicalArithmeticCocycle
        (cuspClassicalFormMap cusp halfWeight negative vector) degree weight_eq even twist parity sign matrix) := rfl

theorem cuspClassicalFiniteAverageFamily_arithmetic_analyticAt (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ)
    (vector : cuspClassicalVectors cusp halfWeight) (exponent : ℂ) (convergent : 3 < exponent.re) :
    AnalyticAt ℂ (fun exponent => functional (classicalArithmeticCocycle
      (cuspClassicalFormMap cusp halfWeight negative
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent vector))
      degree weight_eq even twist parity sign matrix)) exponent := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  let coefficient := (cuspClassicalArithmeticCocycleCoefficient cusp halfWeight negative degree
    weight_eq even twist parity sign matrix functional).toContinuousLinearMap
  let evaluation := ContinuousLinearMap.apply ℂ (cuspClassicalVectors cusp halfWeight) vector
  exact ((coefficient.comp evaluation).analyticAt _).comp
    (cuspClassicalFiniteAverageFamily_analyticAt cusp central_positive halfWeight negative exponent convergent)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
