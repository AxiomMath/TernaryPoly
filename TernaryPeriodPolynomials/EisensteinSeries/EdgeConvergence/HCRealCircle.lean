module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCRealMode
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalScalar
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticFamily
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.EndpointLift
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Inputs

@[expose] public section


/-!
# The Cauchy circle lift of the local standard integrals realizes the circle average

Original work by Claude Sonnet 5.5.

Let `L_s = ∫_{(ℝ × ℚ₃)²} v_s(w⁻¹ n(u) g) du` be the local Hilbert standard integral of a flat family at
an argument `g` with integral finite part, for `s` in the closed disc `|s - s₀| ≤ r` inside
`Re s > -n/2 - 1`, and let `m` be continuous on the circle. If a smooth vector `W` is the Cauchy lift
`(2πi)⁻¹ ∮ (s-s₀)⁻¹ (m(s) • L_s) ds` (`EndpointLift.endpointLift`), then
`realize W B = (2πi)⁻¹ ∮ (s-s₀)⁻¹ m(s) ∫ realize (v_s(w⁻¹ n(u) g)) B du ds`
(`circle_lift_realizes`).

The vectors `m(γ θ) • L_{γ θ}` (`γ` the parametrization of the circle) are smooth, fixed by the
principal congruence subgroup (`localValue_fixed`), continuous in the Hilbert space in `θ`
(`localValue_analyticAt_halfPlane`), with realizations bounded uniformly in `θ` (the strip majorant
`localScalarIntegrand_bound`) and continuous in `θ` (`localScalarIntegral_analyticAt`), so that
`HCReal.realize_integral_of_fixed` applies to `2π • W`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace HCReal

/-- **Realization of the Cauchy circle lift.** -/
theorem circle_lift_realizes {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (center : ℂ) (radius : ℝ) (radiusPositive : 0 < radius)
    (ballSubset : Metric.closedBall center radius ⊆ EdgeInputs.localHalfPlane degree)
    (multiplier : ℂ → ℂ) (multiplierContinuous : ContinuousOn multiplier (Metric.sphere center radius))
    (argument : AdelicGL) (integral : argument ∈ integralArguments)
    (lift : data.cusp.smooth)
    (liftEquation : lift.val = EndpointLift.endpointLift center radius multiplier
      (fun parameter => localValue data parameter (extension parameter) (flat.1 parameter)
        argument))
    (binary : BinaryAdelicGL) :
    (∀ unit : BinaryLevel.finiteCongruence,
      data.cusp.π (atFinite unit.val) lift.val = lift.val) ∧
    data.cusp.realize lift binary =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(center, radius),
        (parameter - center)⁻¹ • (multiplier parameter • ∫ coordinates,
          localScalarIntegrand data parameter (extension parameter) (flat.1 parameter) argument
            binary coordinates ∂localRadicalMeasure) := by
  have onSphere : ∀ θ : ℝ, circleMap center radius θ ∈ Metric.sphere center radius :=
    fun θ => circleMap_mem_sphere center radiusPositive.le θ
  have halfPlane : ∀ θ : ℝ, -(degree : ℝ) / 2 - 1 < (circleMap center radius θ).re :=
    fun θ => ballSubset (Metric.sphere_subset_closedBall (onSphere θ))
  have integralPair := integral
  obtain ⟨integralArgument, finite⟩ := integralPair
  -- uniform bounds on the circle
  obtain ⟨multiplierBound, multiplierBounded⟩ :=
    (isCompact_sphere center radius).exists_bound_of_continuousOn multiplierContinuous
  have circleNonempty : (Metric.sphere center radius).Nonempty :=
    ⟨circleMap center radius 0, onSphere 0⟩
  obtain ⟨minimum, minimumMembership, minimal⟩ :=
    (isCompact_sphere center radius).exists_isMinOn circleNonempty
      Complex.continuous_re.continuousOn
  obtain ⟨maximum, _, maximal⟩ :=
    (isCompact_sphere center radius).exists_isMaxOn circleNonempty
      Complex.continuous_re.continuousOn
  have lowerHalfPlane : -(degree : ℝ) / 2 - 1 < minimum.re :=
    ballSubset (Metric.sphere_subset_closedBall minimumMembership)
  have lowerBound : ∀ θ : ℝ, minimum.re ≤ (circleMap center radius θ).re :=
    fun θ => isMinOn_iff.mp minimal _ (onSphere θ)
  have upperBound : ∀ θ : ℝ, (circleMap center radius θ).re ≤ maximum.re :=
    fun θ => isMaxOn_iff.mp maximal _ (onSphere θ)
  have ordered : minimum.re ≤ maximum.re :=
    (lowerBound 0).trans (upperBound 0)
  obtain ⟨scalarConstant, _, scalarBounded⟩ := localScalarIntegrand_bound data extension flat
    minimum.re maximum.re lowerHalfPlane ordered argument integral
  have majorantIntegrable := hcMajorant_integrable (degree := degree) minimum.re scalarConstant
    lowerHalfPlane
  have integralBound : ∀ (θ : ℝ) (test : BinaryAdelicGL),
      ‖∫ coordinates, localScalarIntegrand data (circleMap center radius θ)
        (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ)) argument
        test coordinates ∂localRadicalMeasure‖ ≤
      ∫ coordinates, hcMajorant degree minimum.re scalarConstant coordinates
        ∂localRadicalMeasure := by
    intro θ test
    exact norm_integral_le_of_norm_le majorantIntegrable (Filter.Eventually.of_forall
      (fun coordinates => scalarBounded _ (lowerBound θ) (upperBound θ) test coordinates))
  -- the smooth vectors
  obtain ⟨rawVector, rawValue⟩ : ∃ raw : ℝ → data.cusp.smooth, ∀ θ,
      (raw θ).val = localValue data (circleMap center radius θ)
        (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ))
        argument :=
    ⟨fun θ => ⟨localValue data (circleMap center radius θ) (extension (circleMap center radius θ))
        (flat.1 (circleMap center radius θ)) argument,
      localValue_mem_smooth data (circleMap center radius θ)
        (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ))
        (halfPlane θ) argument integral⟩, fun θ => rfl⟩
  have rawRealize : ∀ (θ : ℝ) (test : BinaryAdelicGL), data.cusp.realize (rawVector θ) test =
      ∫ coordinates, localScalarIntegrand data (circleMap center radius θ)
        (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ)) argument
        test coordinates ∂localRadicalMeasure := by
    intro θ test
    have vectorEquality : rawVector θ = ⟨localValue data (circleMap center radius θ)
        (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ)) argument,
        localValue_mem_smooth data (circleMap center radius θ)
          (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ))
          (halfPlane θ) argument integral⟩ := Subtype.ext (rawValue θ)
    rw [vectorEquality]
    exact localValue_realizes data extension flat (circleMap center radius θ) (halfPlane θ)
      argument integral test
  -- continuity in the circle parameter
  have circleContinuous : Continuous (circleMap center radius) := continuous_circleMap center radius
  have multiplierComposite : Continuous (fun θ : ℝ => multiplier (circleMap center radius θ)) :=
    multiplierContinuous.comp_continuous circleContinuous onSphere
  have valueContinuous : Continuous (fun θ : ℝ => localValue data (circleMap center radius θ)
      (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ)) argument) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have analytic := localValue_analyticAt_halfPlane data extension flat argument
      (-(degree : ℝ) / 2 - 1)
      (fun real above => localIntegrand_integrable data (real : ℂ) (extension (real : ℂ))
        (flat.1 (real : ℂ)) (by rw [Complex.ofReal_re]; exact above) argument integralArgument
        finite)
      (circleMap center radius θ) (halfPlane θ)
    exact ContinuousAt.comp' (f := circleMap center radius)
      (g := fun parameter : ℂ => localValue data parameter (extension parameter)
        (flat.1 parameter) argument) (x := θ) analytic.continuousAt circleContinuous.continuousAt
  have scalarContinuous : ∀ test : BinaryAdelicGL, Continuous (fun θ : ℝ =>
      ∫ coordinates, localScalarIntegrand data (circleMap center radius θ)
        (extension (circleMap center radius θ)) (flat.1 (circleMap center radius θ)) argument
        test coordinates ∂localRadicalMeasure) := by
    intro test
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact ContinuousAt.comp' (f := circleMap center radius)
      (g := fun spectral : ℂ => ∫ coordinates, localScalarIntegrand data spectral
        (extension spectral) (flat.1 spectral) argument test coordinates ∂localRadicalMeasure)
      (x := θ) (localScalarIntegral_analyticAt data extension flat (circleMap center radius θ)
        (halfPlane θ) argument integral test).continuousAt circleContinuous.continuousAt
  -- the family of integrands
  obtain ⟨family, familyValue⟩ : ∃ family : ℝ → data.cusp.smooth, ∀ θ,
      family θ = multiplier (circleMap center radius θ) • rawVector θ :=
    ⟨fun θ => multiplier (circleMap center radius θ) • rawVector θ, fun θ => rfl⟩
  have familyHilbert : ∀ θ : ℝ, (family θ).val = multiplier (circleMap center radius θ) •
      localValue data (circleMap center radius θ) (extension (circleMap center radius θ))
        (flat.1 (circleMap center radius θ)) argument := by
    intro θ
    rw [familyValue]
    change multiplier (circleMap center radius θ) • (rawVector θ).val = _
    rw [rawValue]
  have familyRealize : ∀ (θ : ℝ) (test : BinaryAdelicGL), data.cusp.realize (family θ) test =
      multiplier (circleMap center radius θ) • ∫ coordinates, localScalarIntegrand data
        (circleMap center radius θ) (extension (circleMap center radius θ))
        (flat.1 (circleMap center radius θ)) argument test coordinates ∂localRadicalMeasure := by
    intro θ test
    rw [familyValue, map_smul, Pi.smul_apply, rawRealize]
  have familyBounded : ∀ (θ : ℝ) (test : BinaryAdelicGL),
      ‖data.cusp.realize (family θ) test‖ ≤ multiplierBound * ∫ coordinates,
        hcMajorant degree minimum.re scalarConstant coordinates ∂localRadicalMeasure := by
    intro θ test
    rw [familyRealize, norm_smul]
    exact mul_le_mul (multiplierBounded _ (onSphere θ)) (integralBound θ test) (norm_nonneg _)
      ((norm_nonneg _).trans (multiplierBounded _ (onSphere θ)))
  have familyMeasurable : ∀ test : BinaryAdelicGL,
      Measurable (fun θ : ℝ => data.cusp.realize (family θ) test) := by
    intro test
    have equality : (fun θ : ℝ => data.cusp.realize (family θ) test) = fun θ =>
        multiplier (circleMap center radius θ) • ∫ coordinates, localScalarIntegrand data
          (circleMap center radius θ) (extension (circleMap center radius θ))
          (flat.1 (circleMap center radius θ)) argument test coordinates ∂localRadicalMeasure :=
      funext (fun θ => familyRealize θ test)
    rw [equality]
    exact (multiplierComposite.smul (scalarContinuous test)).measurable
  have familyFixed : ∀ (θ : ℝ) (unit : BinaryLevel.finiteCongruence),
      data.cusp.π (atFinite unit.val) (family θ).val = (family θ).val := by
    intro θ unit
    rw [familyHilbert, map_smul]
    congr 1
    exact localValue_fixed data (circleMap center radius θ) (extension (circleMap center radius θ))
      (flat.1 (circleMap center radius θ)) argument
      ⟨unit.val, principal_le_level_of_integral argument integral unit.property⟩
  have hilbertContinuous : Continuous (fun θ : ℝ => (family θ).val) := by
    have equality : (fun θ : ℝ => (family θ).val) = fun θ => multiplier (circleMap center radius θ) •
        localValue data (circleMap center radius θ) (extension (circleMap center radius θ))
          (flat.1 (circleMap center radius θ)) argument := funext familyHilbert
    rw [equality]
    exact multiplierComposite.smul valueContinuous
  have hilbertIntegrable : Integrable (fun θ : ℝ => (family θ).val)
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) := hilbertContinuous.integrableOn_Ioc
  have _finiteMeasure : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  -- the total vector
  obtain ⟨total, totalValue⟩ : ∃ total : data.cusp.smooth,
      total = ((2 * Real.pi : ℝ) : ℂ) • lift := ⟨_, rfl⟩
  have averageEquation : lift.val = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
      ∫ θ in (0 : ℝ)..2 * Real.pi, multiplier (circleMap center radius θ) •
        localValue data (circleMap center radius θ) (extension (circleMap center radius θ))
          (flat.1 (circleMap center radius θ)) argument := by
    rw [liftEquation, EndpointLift.endpointLift_eq_circleAverage radiusPositive,
      Real.circleAverage_def]
    exact (Complex.coe_smul _ _).symm
  have totalEquation : total.val = ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), (family θ).val := by
    rw [totalValue]
    change ((2 * Real.pi : ℝ) : ℂ) • lift.val = _
    rw [averageEquation, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (show (2 * Real.pi) ≠ 0 by positivity), Complex.ofReal_one, one_smul,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    exact (familyHilbert θ).symm
  have liftFixed : ∀ unit : BinaryLevel.finiteCongruence,
      data.cusp.π (atFinite unit.val) lift.val = lift.val := by
    intro unit
    have scaled : lift.val = (((2 * Real.pi : ℝ) : ℂ))⁻¹ • total.val := by
      rw [totalValue]
      change lift.val = (((2 * Real.pi : ℝ) : ℂ))⁻¹ • (((2 * Real.pi : ℝ) : ℂ) • lift.val)
      rw [smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
        (show (2 * Real.pi) ≠ 0 by positivity)), one_smul]
    rw [scaled, map_smul, integral_fixed data (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))
      family familyFixed total totalEquation unit]
  have realized := realize_integral_of_fixed data
    (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) family familyFixed hilbertIntegrable total
    totalEquation (multiplierBound * ∫ coordinates,
      hcMajorant degree minimum.re scalarConstant coordinates ∂localRadicalMeasure)
    familyBounded familyMeasurable binary
  have integrandEquation : (fun θ : ℝ => data.cusp.realize (family θ) binary) = fun θ =>
      multiplier (circleMap center radius θ) • ∫ coordinates, localScalarIntegrand data
        (circleMap center radius θ) (extension (circleMap center radius θ))
        (flat.1 (circleMap center radius θ)) argument binary coordinates ∂localRadicalMeasure :=
    funext (fun θ => familyRealize θ binary)
  rw [totalValue, map_smul, Pi.smul_apply, smul_eq_mul, integrandEquation] at realized
  have key : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(center, radius),
      (parameter - center)⁻¹ • (multiplier parameter • ∫ coordinates,
        localScalarIntegrand data parameter (extension parameter) (flat.1 parameter) argument
          binary coordinates ∂localRadicalMeasure) =
      Real.circleAverage (fun parameter => multiplier parameter • ∫ coordinates,
        localScalarIntegrand data parameter (extension parameter) (flat.1 parameter) argument
          binary coordinates ∂localRadicalMeasure) center radius :=
    EndpointLift.endpointLift_eq_circleAverage radiusPositive multiplier
      (fun parameter => ∫ coordinates, localScalarIntegrand data parameter (extension parameter)
        (flat.1 parameter) argument binary coordinates ∂localRadicalMeasure)
  have averageForm : Real.circleAverage (fun parameter => multiplier parameter • ∫ coordinates,
        localScalarIntegrand data parameter (extension parameter) (flat.1 parameter) argument
          binary coordinates ∂localRadicalMeasure) center radius =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
        multiplier (circleMap center radius θ) • ∫ coordinates, localScalarIntegrand data
          (circleMap center radius θ) (extension (circleMap center radius θ))
          (flat.1 (circleMap center radius θ)) argument binary coordinates
            ∂localRadicalMeasure := by
    rw [Real.circleAverage_def,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
    exact Complex.real_smul
  refine ⟨liftFixed, ?_⟩
  rw [key, averageForm, ← realized, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (show (2 * Real.pi) ≠ 0 by positivity), Complex.ofReal_one, one_mul]

end HCReal

end TernaryPeriodPolynomials.EdgeConvergence
