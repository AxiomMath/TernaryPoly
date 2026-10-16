module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.EulerCommutation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicIntegral_classicalEuler_real (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (place : FinitePlace) (exponent : ℂ) (convergent : 2 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) (real : BinaryRealGL) (base : BinaryFiniteGL) :
    (∫ pair, cuspLocalPadicIntegrand cusp (cuspSmoothAction cusp (atInfinity real) vector.val) base place exponent pair
      ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
      normPower (GeneralLinearGroup.det (atFinite base)) exponent *
        cusp.realize (cuspSmoothAction cusp (atInfinity real)
          (cuspClassicalLocalEulerEquiv cusp central_positive halfWeight negative place exponent convergent vector).val)
          (atFinite base) := by
  let denominator := cuspClassicalEulerDenominatorEquiv cusp central_positive halfWeight negative place exponent convergent
  let preimage := denominator.symm vector
  have mapped : cuspLocalPadicEulerDenominatorOperator cusp place exponent preimage.val = vector.val :=
    congrArg Subtype.val (denominator.apply_symm_apply vector)
  have identity := cuspLocalPadicIntegral_denominatorOperator cusp
    (cuspSmoothAction cusp (atInfinity real) preimage.val)
    (cuspSmoothAction_real_spherical cusp preimage.val preimage.property.1 real) base place exponent convergent
  rw [cuspLocalPadicEulerDenominatorOperator_real_commute, mapped,
    cuspLocalPadicEulerNumeratorOperator_eq_shift, cuspLocalPadicEulerDenominatorOperator_real_commute] at identity
  exact identity

end TernaryPeriodPolynomials.SphericalDetection.Helpers
