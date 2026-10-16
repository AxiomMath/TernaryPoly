module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodHeckeKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.ParityKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.ArithmeticPeriodMap

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalFormMap_hecke (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (prime : Nat.Primes)
    (vector : cuspClassicalVectors cusp halfWeight) :
    (cuspClassicalFormMap cusp halfWeight negative
      (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) : UpperHalfPlane → ℂ) =
        scalarPrimeHecke halfWeight prime (cuspClassicalFormMap cusp halfWeight negative vector) := by
  rw [cuspClassicalFormMap_coe, cuspClassicalFormMap_coe]
  exact cuspPrimeHeckeSum_scalar_intertwines cusp central_positive halfWeight prime vector.val vector.property.2.1

theorem cuspClassicalArithmeticPeriodMap_hecke_kernel (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight)
    (zero : cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity sign vector = 0) :
    cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity sign
      (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) = 0 := by
  rw [cuspClassicalArithmeticPeriodMap_apply, classicalArithmeticCocycle,
    arithmeticParityCocycle_H1_zero_iff] at zero ⊢
  exact classicalParityPeriod_hecke_kernel halfWeight _ _ degree weight_eq even twist parity prime
    (cuspClassicalFormMap_hecke cusp central_positive halfWeight negative prime vector) zero

/-- Each compatible arithmetic period map detects every classical vector. -/
theorem cuspClassicalArithmeticPeriodMap_injective (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity.val) :
    Function.Injective (cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity.val sign) :=
  cuspClassicalArithmeticPeriodMap_injective_of_hecke_stable cusp central_positive halfWeight negative
    degree weight_eq even twist parity sign
    (cuspClassicalArithmeticPeriodMap_hecke_kernel cusp central_positive halfWeight negative degree weight_eq
      even twist parity.val sign)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
