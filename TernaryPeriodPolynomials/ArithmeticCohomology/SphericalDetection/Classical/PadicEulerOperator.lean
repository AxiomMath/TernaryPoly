module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerOperators
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.HeckeFaithfulness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspClassicalVectors_finiteDimensional (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) := by
  let : FiniteDimensional ℂ ((cuspScalarWeightedLinear cusp halfWeight 1).comp
      (cuspClassicalVectors cusp halfWeight).subtype).range :=
    cuspClassicalScalarImage_finiteDimensional cusp halfWeight negative
  exact FiniteDimensional.of_injective
    (((cuspScalarWeightedLinear cusp halfWeight 1).comp (cuspClassicalVectors cusp halfWeight).subtype).rangeRestrict)
    (fun first second equal => cuspClassicalScalarMap_injective cusp central_positive halfWeight
      (congrArg Subtype.val equal))

theorem cuspLocalPadicSphereOperator_one_classical (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (place : FinitePlace) (vector : cusp.smooth)
    (classical_vector : vector ∈ cuspClassicalVectors cusp halfWeight) :
    cuspLocalPadicSphereOperator cusp place 1 vector ∈ cuspClassicalVectors cusp halfWeight := by
  rw [cuspLocalPadicSphereOperator_one cusp vector classical_vector.1 place]
  exact (cuspClassicalVectors cusp halfWeight).smul_mem _
    (cuspPrimeHeckeSum_classical cusp central_positive halfWeight _ vector classical_vector)

theorem cuspLocalPadicEulerDenominatorOperator_classical (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (place : FinitePlace) (exponent : ℂ) (vector : cusp.smooth)
    (classical_vector : vector ∈ cuspClassicalVectors cusp halfWeight) :
    cuspLocalPadicEulerDenominatorOperator cusp place exponent vector ∈ cuspClassicalVectors cusp halfWeight :=
  (cuspClassicalVectors cusp halfWeight).sub_mem ((cuspClassicalVectors cusp halfWeight).smul_mem _ classical_vector)
    ((cuspClassicalVectors cusp halfWeight).smul_mem _
      (cuspLocalPadicSphereOperator_one_classical cusp central_positive halfWeight place vector classical_vector))

def cuspClassicalEulerDenominator (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (place : FinitePlace) (exponent : ℂ) :
    Module.End ℂ (cuspClassicalVectors cusp halfWeight) :=
  (cuspLocalPadicEulerDenominatorOperator cusp place exponent).restrict
    (cuspLocalPadicEulerDenominatorOperator_classical cusp central_positive halfWeight place exponent)

theorem cuspClassicalEulerDenominator_injective (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re) :
    Function.Injective (cuspClassicalEulerDenominator cusp central_positive halfWeight place exponent) := by
  intro first second equal
  apply sub_eq_zero.mp
  by_contra nonzero
  have difference_nonzero : (first - second).val ≠ 0 := fun zero => nonzero (Subtype.ext zero)
  have mapped_zero := congrArg Subtype.val (show cuspClassicalEulerDenominator cusp central_positive halfWeight place exponent
      (first - second) = 0 by rw [map_sub, equal, sub_self])
  exact cuspLocalPadicEulerDenominatorOperator_ne_zero cusp place exponent convergent (first - second).val
    (first - second).property.1 difference_nonzero mapped_zero

def cuspClassicalEulerDenominatorEquiv (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re) :
    cuspClassicalVectors cusp halfWeight ≃ₗ[ℂ] cuspClassicalVectors cusp halfWeight := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  have injective := cuspClassicalEulerDenominator_injective cusp central_positive halfWeight place exponent convergent
  exact LinearEquiv.ofBijective (cuspClassicalEulerDenominator cusp central_positive halfWeight place exponent)
    ⟨injective, LinearMap.injective_iff_surjective.mp injective⟩

theorem cuspClassicalEulerDenominatorEquiv_apply (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) :
    (cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent vector).val =
      cuspLocalPadicEulerDenominatorOperator cusp place exponent vector.val := rfl

def cuspClassicalLocalEulerEquiv (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re) :
    cuspClassicalVectors cusp halfWeight ≃ₗ[ℂ] cuspClassicalVectors cusp halfWeight :=
  (cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent).symm.trans
    (cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place (exponent + 1)
      (by simp only [Complex.add_re, Complex.one_re]; linarith))

theorem cuspLocalPadicIntegral_classicalEuler (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) (base : BinaryFiniteGL) :
    (∫ pair, cuspLocalPadicIntegrand cusp vector.val base place exponent pair
      ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
      normPower (GeneralLinearGroup.det (atFinite base)) exponent *
        cusp.realize (cuspClassicalLocalEulerEquiv cusp central_positive halfWeight negative place exponent convergent vector).val
          (atFinite base) := by
  let denominator := cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent
  let preimage := denominator.symm vector
  have mapped : cuspLocalPadicEulerDenominatorOperator cusp place exponent preimage.val = vector.val :=
    congrArg Subtype.val (denominator.apply_symm_apply vector)
  have identity := cuspLocalPadicIntegral_denominatorOperator cusp preimage.val preimage.property.1 base place exponent convergent
  rw [mapped, cuspLocalPadicEulerNumeratorOperator_eq_shift] at identity
  exact identity

end TernaryPeriodPolynomials.SphericalDetection.Helpers
