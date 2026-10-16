module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PadicEulerOperator
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteEigenDetection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspClassicalPrimeHecke (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (prime : Nat.Primes) : Module.End ℂ (cuspClassicalVectors cusp halfWeight) :=
  (cuspPrimeHeckeSum cusp prime).restrict (cuspPrimeHeckeSum_classical cusp central_positive halfWeight prime)

theorem cuspLocalPadicSphereOperator_one_hecke_commute (cusp : CuspidalRepresentation) (place : FinitePlace)
    (prime : Nat.Primes) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    cuspLocalPadicSphereOperator cusp place 1 (cuspPrimeHeckeSum cusp prime vector) =
      cuspPrimeHeckeSum cusp prime (cuspLocalPadicSphereOperator cusp place 1 vector) := by
  rw [cuspLocalPadicSphereOperator_one cusp _ (cuspPrimeHeckeSum_spherical cusp prime vector spherical) place,
    cuspLocalPadicSphereOperator_one cusp vector spherical place, map_smul,
    cuspPrimeHeckeSum_commute cusp _ prime vector spherical]

theorem cuspLocalPadicEulerDenominatorOperator_hecke_commute (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) (prime : Nat.Primes) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    cuspLocalPadicEulerDenominatorOperator cusp place exponent (cuspPrimeHeckeSum cusp prime vector) =
      cuspPrimeHeckeSum cusp prime (cuspLocalPadicEulerDenominatorOperator cusp place exponent vector) := by
  simp only [cuspLocalPadicEulerDenominatorOperator, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, cuspLocalPadicSphereOperator_one_hecke_commute cusp place prime vector spherical]

theorem cuspClassicalEulerDenominatorEquiv_hecke_commute (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re)
    (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent
        (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) =
      cuspClassicalPrimeHecke cusp central_positive halfWeight prime
        (cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent vector) := by
  apply Subtype.ext
  exact cuspLocalPadicEulerDenominatorOperator_hecke_commute cusp place exponent prime vector.val vector.property.1

theorem cuspClassicalEulerDenominatorEquiv_symm_hecke_commute (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re)
    (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight) :
    (cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent).symm
        (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) =
      cuspClassicalPrimeHecke cusp central_positive halfWeight prime
        ((cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent).symm vector) := by
  apply (cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent).injective
  rw [LinearEquiv.apply_symm_apply, cuspClassicalEulerDenominatorEquiv_hecke_commute, LinearEquiv.apply_symm_apply]

theorem cuspClassicalLocalEulerEquiv_hecke_commute (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re)
    (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalLocalEulerEquiv cusp central_positive halfWeight negative place exponent convergent
        (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) =
      cuspClassicalPrimeHecke cusp central_positive halfWeight prime
        (cuspClassicalLocalEulerEquiv cusp central_positive halfWeight negative place exponent convergent vector) := by
  rw [cuspClassicalLocalEulerEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    cuspClassicalEulerDenominatorEquiv_symm_hecke_commute, cuspClassicalEulerDenominatorEquiv_hecke_commute]

theorem cuspLocalPadicEulerDenominatorOperator_real_commute (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) (real : BinaryRealGL) (vector : cusp.smooth) :
    cuspLocalPadicEulerDenominatorOperator cusp place exponent (cuspSmoothAction cusp (atInfinity real) vector) =
      cuspSmoothAction cusp (atInfinity real) (cuspLocalPadicEulerDenominatorOperator cusp place exponent vector) := by
  simp only [cuspLocalPadicEulerDenominatorOperator, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, cuspLocalPadicSphereOperator_real_commute]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
