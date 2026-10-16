module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerOperatorRelation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspLocalPadicEulerDenominatorOperator (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) : Module.End ℂ cusp.smooth :=
  let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
  let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
  (1 + prime * cuspLocalPadicCentralChar cusp place * scale ^ 2) • 1 -
    scale • cuspLocalPadicSphereOperator cusp place 1

def cuspLocalPadicEulerNumeratorOperator (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) : Module.End ℂ cusp.smooth :=
  let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
  let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
  (1 + cuspLocalPadicCentralChar cusp place / prime * scale ^ 2) • 1 -
    (scale / prime) • cuspLocalPadicSphereOperator cusp place 1

theorem cuspLocalPadicEulerDenominatorOperator_spherical (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    (cuspLocalPadicEulerDenominatorOperator cusp place exponent vector).val ∈ cuspSphericalValues cusp :=
  (cuspSphericalValues cusp).sub_mem ((cuspSphericalValues cusp).smul_mem _ spherical)
    ((cuspSphericalValues cusp).smul_mem _ (cuspLocalPadicSphereOperator_one_spherical cusp place vector spherical))

theorem cuspLocalPadicEulerNumeratorOperator_eq_shift (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) : cuspLocalPadicEulerNumeratorOperator cusp place exponent =
      cuspLocalPadicEulerDenominatorOperator cusp place (exponent + 1) := by
  unfold cuspLocalPadicEulerNumeratorOperator cuspLocalPadicEulerDenominatorOperator
  rw [padicPrimitiveSeriesScale_add_one _ (Rat.HeightOneSpectrum.primesEquiv place).property.pos]
  have nonzero : ((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero
  field_simp

theorem cuspLocalPadicEulerNumeratorOperator_spherical (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    (cuspLocalPadicEulerNumeratorOperator cusp place exponent vector).val ∈ cuspSphericalValues cusp := by
  rw [cuspLocalPadicEulerNumeratorOperator_eq_shift]
  exact cuspLocalPadicEulerDenominatorOperator_spherical cusp place (exponent + 1) vector spherical

theorem cuspLocalPadicIntegral_denominatorOperator (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) :
    (∫ pair, cuspLocalPadicIntegrand cusp (cuspLocalPadicEulerDenominatorOperator cusp place exponent vector)
      base place exponent pair ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
      normPower (GeneralLinearGroup.det (atFinite base)) exponent *
        cusp.realize (cuspLocalPadicEulerNumeratorOperator cusp place exponent vector) (atFinite base) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
  let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
  let central := cuspLocalPadicCentralChar cusp place
  have equality (pair) :
      cuspLocalPadicIntegrand cusp (cuspLocalPadicEulerDenominatorOperator cusp place exponent vector)
        base place exponent pair =
      (1 + prime * central * scale ^ 2) * cuspLocalPadicIntegrand cusp vector base place exponent pair -
        scale * cuspLocalPadicIntegrand cusp (cuspLocalPadicSphereOperator cusp place 1 vector) base place exponent pair := by
    simp only [cuspLocalPadicIntegrand, cuspLocalPadicEulerDenominatorOperator, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [prime, central, scale]
    ring
  simp_rw [equality]
  rw [integral_sub
    ((cuspLocalPadicIntegrand_integrable cusp vector spherical base place exponent convergent).const_mul _)
    ((cuspLocalPadicIntegrand_integrable cusp (cuspLocalPadicSphereOperator cusp place 1 vector)
      (cuspLocalPadicSphereOperator_one_spherical cusp place vector spherical) base place exponent convergent).const_mul _),
    integral_const_mul, integral_const_mul,
    cuspLocalPadicIntegral_operator_relation cusp vector spherical base place exponent convergent]
  simp only [cuspLocalPadicEulerNumeratorOperator, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem cuspLocalPadicEulerDenominatorOperator_ne_zero (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (nonzero : vector ≠ 0) :
    cuspLocalPadicEulerDenominatorOperator cusp place exponent vector ≠ 0 := by
  let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
  let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
  let central := cuspLocalPadicCentralChar cusp place
  have scale_nonzero : scale ≠ 0 := mul_ne_zero
    (Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero) (Complex.exp_ne_zero _)
  intro zero
  change (1 + prime * central * scale ^ 2) • vector - scale • cuspLocalPadicSphereOperator cusp place 1 vector = 0 at zero
  have action := (sub_eq_zero.mp zero).symm
  have eigen : cuspLocalPadicSphereOperator cusp place 1 vector =
      ((1 + prime * central * scale ^ 2) / scale) • vector := by
    calc
      _ = scale⁻¹ • (scale • cuspLocalPadicSphereOperator cusp place 1 vector) := by
        rw [smul_smul, inv_mul_cancel₀ scale_nonzero, one_smul]
      _ = _ := by rw [action, smul_smul, div_eq_mul_inv, mul_comm]
  have denominator := cuspLocalPadicEulerDenominator_ne_zero cusp vector nonzero spherical place exponent convergent _ eigen
  apply denominator
  change 1 - (1 + prime * central * scale ^ 2) / scale * scale + prime * central * scale ^ 2 = 0
  field_simp
  ring

theorem cuspLocalPadicEulerNumeratorOperator_ne_zero (cusp : CuspidalRepresentation) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (nonzero : vector ≠ 0) :
    cuspLocalPadicEulerNumeratorOperator cusp place exponent vector ≠ 0 := by
  rw [cuspLocalPadicEulerNumeratorOperator_eq_shift]
  exact cuspLocalPadicEulerDenominatorOperator_ne_zero cusp place (exponent + 1)
    (by simp only [Complex.add_re, Complex.one_re]; linarith) vector spherical nonzero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
