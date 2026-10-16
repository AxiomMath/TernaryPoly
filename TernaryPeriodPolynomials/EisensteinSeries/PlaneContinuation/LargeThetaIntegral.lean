module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.NonzeroGodementUnfolding
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PositiveLaplaceIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTheta
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LargeThetaIntegral

def height (binary : BinaryAdelicGL) : ℝ := Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ)

def largeSet : Set BinaryAdelicGL := {binary | 1 ≤ (adeleNorm (GeneralLinearGroup.det binary) : ℝ)}

def domain : Set BinaryAdelicGL := BinaryFundamentalDomain.domain ∩ largeSet

theorem height_measurable : Measurable height :=
  Real.measurable_log.comp (AdelicNormMeasurable.norm_measurable.comp WeightedAbsoluteTheta.determinant_continuous.measurable)

theorem largeSet_measurable : MeasurableSet largeSet :=
  measurableSet_le measurable_const (AdelicNormMeasurable.norm_measurable.comp WeightedAbsoluteTheta.determinant_continuous.measurable)

theorem domain_measurable : MeasurableSet domain := BinaryFundamentalDomain.domain_measurable.inter largeSet_measurable

theorem height_nonnegative (binary : BinaryAdelicGL) (membership : binary ∈ domain) : 0 ≤ height binary :=
  Real.log_nonneg membership.2

def integrand {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (point : AdelicGL) (parameter : ℂ) (binary : BinaryAdelicGL) : ℂ :=
  (fullTheta test point binary - test 0) * innerCharacter data parameter (GeneralLinearGroup.det binary) * data.cusp.realize vector binary

theorem character_factor {degree : ℕ} (data : InducingData degree) (parameter : ℂ) (scalar : Adelesˣ) :
    innerCharacter data parameter scalar = innerCharacter data 0 scalar *
      Complex.exp (parameter * (Real.log (adeleNorm scalar : ℝ) : ℂ)) := by
  have exponent : binaryInductionExponent degree .plane parameter + 2 * inductionExponent .plane parameter =
      (binaryInductionExponent degree .plane 0 + 2 * inductionExponent .plane 0) + parameter := by
    simp only [binaryInductionExponent, inductionExponent]
    ring
  change (data.chi.toMonoidHom scalar)⁻¹ * Complex.exp (_ * (Real.log (adeleNorm scalar : ℝ) : ℂ)) =
    ((data.chi.toMonoidHom scalar)⁻¹ * Complex.exp (_ * (Real.log (adeleNorm scalar : ℝ) : ℂ))) * _
  rw [exponent, add_mul, Complex.exp_add, mul_assoc]

theorem integrand_eq_laplace {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (point : AdelicGL) (parameter : ℂ) (binary : BinaryAdelicGL) :
    integrand data test vector point parameter binary =
      PositiveLaplaceIntegral.integrand (integrand data test vector point 0) height parameter binary := by
  unfold integrand PositiveLaplaceIntegral.integrand height
  rw [character_factor data parameter]
  ring

theorem integrand_measurable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (parameter : ℂ) :
    Measurable (integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point parameter) := by
  have thetaContinuous : Continuous (fun binary => fullTheta (AdelicSchwartzTheta.tensorTest realTest finiteTest) point binary) :=
    (SchwartzThetaContinuity.fullTheta_continuous realTest finiteTest finiteContinuous finiteSupport).comp
    (f := fun binary : BinaryAdelicGL => (point, binary))
    (continuous_const.prodMk (continuous_id : Continuous (fun binary : BinaryAdelicGL => binary)))
  exact ((thetaContinuous.sub continuous_const).measurable.mul
    ((AdelicNormMeasurable.innerCharacter_measurable data parameter).comp WeightedAbsoluteTheta.determinant_continuous.measurable)).mul
      (CuspFunctionContinuity.continuous data.cusp vector).measurable

theorem weighted_integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (exponent : ℝ) :
    IntegrableOn (fun binary => ‖integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point 0 binary‖ *
      Real.exp (exponent * height binary)) domain BinaryHaar.measure := by
  let majorantParameter : ℂ := (max exponent 2 : ℝ)
  have halfPlane : (1 - (degree : ℝ)) / 2 < majorantParameter.re := by
    change (1 - (degree : ℝ)) / 2 < max exponent 2
    have degreeNonnegative : (0 : ℝ) ≤ degree := Nat.cast_nonneg degree
    nlinarith [le_max_right exponent 2]
  have majorantIntegrable : IntegrableOn
      (integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point majorantParameter) domain BinaryHaar.measure :=
    (NonzeroThetaIntegrability.nonzero_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport majorantParameter point
      ((RawGodementIntegrability.halfPlane_iff degree majorantParameter).mpr halfPlane)).mono_set Set.inter_subset_left
  apply majorantIntegrable.norm.mono'
    (((integrand_measurable data vector realTest finiteTest finiteContinuous finiteSupport point 0).norm).mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul height_measurable))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem domain_measurable] with binary membership
  change ‖‖integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point 0 binary‖ *
    Real.exp (exponent * height binary)‖ ≤
      ‖integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point majorantParameter binary‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le),
    integrand_eq_laplace data _ vector point majorantParameter, PositiveLaplaceIntegral.norm_integrand]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (le_max_left exponent 2) (height_nonnegative binary membership))) (norm_nonneg _)

theorem integrable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : AdelicGL) (parameter : ℂ) :
    IntegrableOn (integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point parameter) domain BinaryHaar.measure := by
  have result := PositiveLaplaceIntegral.integrable (BinaryHaar.measure.restrict domain)
    (integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point 0) height
    (integrand_measurable data vector realTest finiteTest finiteContinuous finiteSupport point 0) height_measurable
    (weighted_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport point) parameter
  exact result.congr (Eventually.of_forall (fun binary => (integrand_eq_laplace data _ vector point parameter binary).symm))

def largePart {degree : ℕ} (data : InducingData degree) (test : Rectangular Adeles → ℂ)
    (vector : data.cusp.smooth) (point : AdelicGL) (parameter : ℂ) : ℂ :=
  ∫ binary in domain, integrand data test vector point parameter binary ∂BinaryHaar.measure

theorem differentiable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest) (point : AdelicGL) :
    Differentiable ℂ (largePart data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point) := by
  have equality : largePart data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point =
      fun parameter => ∫ binary in domain,
        PositiveLaplaceIntegral.integrand (integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point 0)
          height parameter binary ∂BinaryHaar.measure := by
    funext parameter
    exact integral_congr_ae (Eventually.of_forall (integrand_eq_laplace data _ vector point parameter))
  rw [equality]
  exact PositiveLaplaceIntegral.differentiable (BinaryHaar.measure.restrict domain)
    (integrand data (AdelicSchwartzTheta.tensorTest realTest finiteTest) vector point 0) height
    (integrand_measurable data vector realTest finiteTest finiteContinuous finiteSupport point 0) height_measurable
    ((ae_restrict_mem domain_measurable).mono height_nonnegative)
    (weighted_integrable data vector fixed realTest finiteTest finiteContinuous finiteSupport point)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LargeThetaIntegral
