module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.CocycleLinearity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.SubmoduleEigenvector

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspClassicalFormMap (cusp : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0) :
    cuspClassicalVectors cusp halfWeight →ₗ[ℂ]
      CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight) :=
  (cuspScalarImageToCuspForm cusp halfWeight negative).comp
    (((cuspScalarWeightedLinear cusp halfWeight 1).comp (cuspClassicalVectors cusp halfWeight).subtype).rangeRestrict)

theorem cuspClassicalFormMap_coe (cusp : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0)
    (vector : cuspClassicalVectors cusp halfWeight) :
    (cuspClassicalFormMap cusp halfWeight negative vector : UpperHalfPlane → ℂ) =
      cuspScalarWeightedLinear cusp halfWeight 1 vector.val :=
  cuspScalarImageForm_coe cusp halfWeight negative _

theorem cuspClassicalFormMap_injective (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) :
    Function.Injective (cuspClassicalFormMap cusp halfWeight negative) := by
  intro first second equal
  apply cuspClassicalScalarMap_injective cusp central_positive halfWeight
  change cuspScalarWeightedLinear cusp halfWeight 1 first.val =
    cuspScalarWeightedLinear cusp halfWeight 1 second.val
  rw [← cuspClassicalFormMap_coe cusp halfWeight negative first,
    ← cuspClassicalFormMap_coe cusp halfWeight negative second, equal]

/-- The actual arithmetic period class attached linearly to each classical vector. -/
def cuspClassicalArithmeticPeriodMap (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity) :
    cuspClassicalVectors cusp halfWeight →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep degree twist) :=
  (groupCohomology.H1π (arithmeticBinaryRep degree twist)).hom.comp
    ((classicalArithmeticCocycleMap (-2 * halfWeight) degree weight_eq even twist parity sign).comp
      (cuspClassicalFormMap cusp halfWeight negative))

theorem cuspClassicalArithmeticPeriodMap_apply (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : ℕ) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity)
    (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity sign vector =
      groupCohomology.H1π (arithmeticBinaryRep degree twist)
        (classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative vector)
          degree weight_eq even twist parity sign) := rfl

theorem cuspClassicalArithmeticPeriodMap_eigen_ne_zero (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity.val)
    (vector : cuspClassicalVectors cusp halfWeight) (nonzero : vector ≠ 0)
    (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight)
      (cuspScalarWeightedLinear cusp halfWeight 1 vector.val) eigenvalues) :
    cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity.val sign vector ≠ 0 := by
  rw [cuspClassicalArithmeticPeriodMap_apply]
  have form_nonzero : cuspClassicalFormMap cusp halfWeight negative vector ≠ 0 := by
    intro zero
    apply nonzero
    exact cuspClassicalFormMap_injective cusp central_positive halfWeight negative (zero.trans (map_zero _).symm)
  apply classicalArithmeticCocycle_H1_ne_zero _ form_nonzero eigenvalues _ degree weight_eq even twist parity sign
  rwa [cuspClassicalFormMap_coe]

/-- Kernel stability is the hypothesis needed to reduce arbitrary vectors to eigenforms. -/
theorem cuspClassicalArithmeticPeriodMap_injective_of_hecke_stable (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (degree : ℕ)
    (weight_eq : -2 * halfWeight = (degree : ℤ) + 2) (even : Even degree)
    (twist : ℤ) (parity : Fin 2) (sign : (-1 : ℂ) ^ twist = (-1 : ℂ) ^ parity.val)
    (stable : ∀ (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight),
      cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity.val sign vector = 0 →
      cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity.val sign
        (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) = 0) :
    Function.Injective (cuspClassicalArithmeticPeriodMap cusp halfWeight negative degree weight_eq even twist parity.val sign) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra nonzero
  obtain ⟨vector, form, eigenvalues, member, vector_nonzero, _form_nonzero, form_eq, relations, _eigen⟩ :=
    cuspClassicalSubmodule_exists_eigenform cusp central_positive halfWeight negative _ nonzero
      (fun prime vector member => stable prime vector member)
  apply cuspClassicalArithmeticPeriodMap_eigen_ne_zero cusp central_positive halfWeight negative degree
    weight_eq even twist parity sign vector (fun zero => vector_nonzero (congrArg Subtype.val zero)) eigenvalues
    (by rwa [form_eq] at relations)
  exact member

end TernaryPeriodPolynomials.SphericalDetection.Helpers
