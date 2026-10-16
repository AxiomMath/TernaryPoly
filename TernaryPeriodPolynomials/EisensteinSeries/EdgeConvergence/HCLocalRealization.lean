module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalMajorant
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalScalarFixed
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.MajorantBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FixedRealizationLimit
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.AdelicIntegral

@[expose] public section


/-!
# The automorphic realization of the local Hilbert standard integral

Original work by Claude Sonnet 5.5.

For a flat family of plane sections, a parameter `s` with `Re s > -n/2 - 1` and an argument `g` with
integral finite part, the realization of the smooth vector `L(g) = ∫_{(ℝ × ℚ₃)²} v_s(w⁻¹ n(u) g) du`
at a binary adele `B` is the integral of the realizations of the integrand,
`∫ realize (v_s(w⁻¹ n(u) g)) B du` (`localValue_realizes`).

The proof is the local analogue of `HilbertScalarLimit.compact_value_realizes`: the integrals over the
compact boxes `localBox N` are smooth vectors realizing the integral of the realizations
(`CompactAdelicIntegral.compact_set_integral`); they converge to `L(g)` in the Hilbert norm
(dominated convergence) and in the sup norm of the realization to the bounded function
`B ↦ ∫ realize (v_s(w⁻¹ n(u) g)) B du` (the strip majorant of `HCLocalMajorant`); both `L(g)` and this
function are fixed by the principal congruence subgroup, so `FixedRealizationLimit.principal_limit_unique`
identifies the limits.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

local instance hcRealizationNormalizedLocalThreeMeasure_isAddHaar :
    normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

instance localRadicalMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts localRadicalMeasure := by
  unfold localRadicalMeasure localLineMeasure
  infer_instance

/-- The power of the local height used as the integrable majorant. -/
def hcMajorant (degree : ℕ) (lower constant : ℝ) (coordinates : LocalLine × LocalLine) : ℝ :=
  constant * localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + lower))

theorem hcMajorant_integrable {degree : ℕ} (lower constant : ℝ)
    (lowerHalfPlane : -(degree : ℝ) / 2 - 1 < lower) :
    Integrable (hcMajorant degree lower constant) localRadicalMeasure :=
  (localHeight_strip_integrable lower lowerHalfPlane).const_mul constant

theorem localScalarIntegrand_bound {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (lower upper : ℝ) (lowerHalfPlane : -(degree : ℝ) / 2 - 1 < lower) (ordered : lower ≤ upper)
    (argument : AdelicGL) (integral : argument ∈ integralArguments) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter : ℂ, lower ≤ parameter.re →
      parameter.re ≤ upper → ∀ (binary : BinaryAdelicGL) (coordinates : LocalLine × LocalLine),
        ‖localScalarIntegrand data parameter (extension parameter) (flat.1 parameter) argument
          binary coordinates‖ ≤ hcMajorant degree lower constant coordinates := by
  obtain ⟨constant, nonnegative, bounded⟩ := localSize_strip_le data extension flat lower upper
    lowerHalfPlane ordered argument integral
  refine ⟨constant, nonnegative, fun parameter lowerBound upperBound binary coordinates => ?_⟩
  exact (realize_le_cuspSupNorm (CuspLift.vector data .plane parameter (extension parameter)
    (flat.1 parameter) (weyl⁻¹ * localRadical coordinates * argument)) binary).trans
    (bounded parameter lowerBound upperBound coordinates)

theorem localScalarIntegrand_integrable {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re)
    (argument : AdelicGL) (integral : argument ∈ integralArguments) (binary : BinaryAdelicGL) :
    Integrable (localScalarIntegrand data parameter (extension parameter) (flat.1 parameter)
      argument binary) localRadicalMeasure := by
  obtain ⟨constant, _, bounded⟩ := localScalarIntegrand_bound data extension flat parameter.re
    parameter.re halfPlane le_rfl argument integral
  exact integrable_of_norm_le_localHeight_rpow _
    (localScalarIntegrand_continuous data parameter (extension parameter) (flat.1 parameter)
      argument binary).aestronglyMeasurable ((degree : ℝ) / 2 + 3 + parameter.re) constant
    (by linarith) (fun coordinates => bounded parameter le_rfl le_rfl binary coordinates)

/-- The compact boxes exhausting the local radical. -/
def localBox (radius : ℕ) : Set (LocalLine × LocalLine) :=
  (Metric.closedBall (0 : ℝ) radius ×ˢ Metric.closedBall (0 : ℚ_[3]) radius) ×ˢ
    (Metric.closedBall (0 : ℝ) radius ×ˢ Metric.closedBall (0 : ℚ_[3]) radius)

theorem localBox_isCompact (radius : ℕ) : IsCompact (localBox radius) :=
  ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))

theorem localBox_measurable (radius : ℕ) : MeasurableSet (localBox radius) :=
  (localBox_isCompact radius).measurableSet

theorem localBox_monotone : Monotone localBox := by
  intro first second order
  have ball : ((first : ℕ) : ℝ) ≤ ((second : ℕ) : ℝ) := Nat.cast_le.mpr order
  exact Set.prod_mono
    (Set.prod_mono (Metric.closedBall_subset_closedBall ball)
      (Metric.closedBall_subset_closedBall ball))
    (Set.prod_mono (Metric.closedBall_subset_closedBall ball)
      (Metric.closedBall_subset_closedBall ball))

theorem localBox_iUnion : (⋃ radius, localBox radius) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro point
  obtain ⟨radius, large⟩ := exists_nat_ge (max (max |point.1.1| ‖point.1.2‖)
    (max |point.2.1| ‖point.2.2‖))
  rw [Set.mem_iUnion]
  refine ⟨radius, ?_⟩
  obtain ⟨firstPair, secondPair⟩ := max_le_iff.mp large
  obtain ⟨firstReal, firstThree⟩ := max_le_iff.mp firstPair
  obtain ⟨secondReal, secondThree⟩ := max_le_iff.mp secondPair
  simp only [localBox, Set.mem_prod, mem_closedBall_zero_iff, Real.norm_eq_abs]
  exact ⟨⟨firstReal, firstThree⟩, ⟨secondReal, secondThree⟩⟩

/-- **Local realization.** The realization of the local Hilbert standard integral at a binary adele
is the integral of the realizations of the integrand. -/
theorem localValue_realizes {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re)
    (argument : AdelicGL) (integral : argument ∈ integralArguments) (binary : BinaryAdelicGL) :
    data.cusp.realize
        ⟨localValue data parameter (extension parameter) (flat.1 parameter) argument,
          localValue_mem_smooth data parameter (extension parameter) (flat.1 parameter) halfPlane
            argument integral⟩ binary =
      ∫ coordinates, localScalarIntegrand data parameter (extension parameter)
        (flat.1 parameter) argument binary coordinates ∂localRadicalMeasure := by
  obtain ⟨constant, _, bounded⟩ := localScalarIntegrand_bound data extension
    flat parameter.re parameter.re halfPlane le_rfl argument integral
  have majorantIntegrable := hcMajorant_integrable (degree := degree) parameter.re constant
    halfPlane
  have scalarIntegrable : ∀ test : BinaryAdelicGL, Integrable
      (localScalarIntegrand data parameter (extension parameter) (flat.1 parameter) argument test)
      localRadicalMeasure :=
    fun test => localScalarIntegrand_integrable data extension flat parameter halfPlane argument
      integral test
  have pointwise : ∀ (test : BinaryAdelicGL) (coordinates : LocalLine × LocalLine),
      ‖localScalarIntegrand data parameter (extension parameter) (flat.1 parameter) argument test
        coordinates‖ ≤ hcMajorant degree parameter.re constant coordinates :=
    fun test coordinates => bounded parameter le_rfl le_rfl test coordinates
  have integralPair := integral
  obtain ⟨integralArgument, finite⟩ := integralPair
  -- the stage vectors
  have stageExists : ∀ radius : ℕ, ∃ vector : data.cusp.smooth,
      vector.val = ∫ point in localBox radius, localIntegrand data parameter (extension parameter)
        (flat.1 parameter) argument point ∂localRadicalMeasure ∧
      ∀ test : BinaryAdelicGL, data.cusp.realize vector test =
        ∫ point in localBox radius, localScalarIntegrand data parameter (extension parameter)
          (flat.1 parameter) argument test point ∂localRadicalMeasure := by
    intro radius
    exact CompactAdelicIntegral.compact_set_integral data parameter (extension parameter)
      (flat.1 parameter) localRadicalMeasure (localBox radius) (localBox radius)
      (localBox_isCompact radius) subset_rfl
      (fun point => weyl⁻¹ * localRadical point * argument)
      ((continuous_const.mul localRadical_continuous).mul continuous_const)
  choose stage stageHilbert stageScalar using stageExists
  -- the target function
  obtain ⟨target, targetApply⟩ : ∃ target : lp (fun _ : BinaryAdelicGL => ℂ) ⊤,
      ∀ test : BinaryAdelicGL, target test = ∫ coordinates, localScalarIntegrand data parameter
        (extension parameter) (flat.1 parameter) argument test coordinates
          ∂localRadicalMeasure := by
    refine ⟨⟨fun test => ∫ coordinates, localScalarIntegrand data parameter (extension parameter)
      (flat.1 parameter) argument test coordinates ∂localRadicalMeasure, memℓp_infty
        ⟨∫ coordinates, hcMajorant degree parameter.re constant coordinates ∂localRadicalMeasure,
          ?_⟩⟩, fun test => rfl⟩
    rintro _ ⟨test, rfl⟩
    exact norm_integral_le_of_norm_le majorantIntegrable
      (Filter.Eventually.of_forall (fun coordinates => pointwise test coordinates))
  -- the Hilbert limit
  have hilbertLimit : Tendsto (fun radius => (stage radius).val) atTop
      (𝓝 (localValue data parameter (extension parameter) (flat.1 parameter) argument)) := by
    have integrableOn : IntegrableOn (localIntegrand data parameter (extension parameter)
        (flat.1 parameter) argument) (⋃ radius, localBox radius) localRadicalMeasure := by
      rw [localBox_iUnion]
      exact integrableOn_univ.mpr (localIntegrand_integrable data parameter (extension parameter)
        (flat.1 parameter) halfPlane argument integralArgument finite)
    have limit := tendsto_setIntegral_of_monotone localBox_measurable localBox_monotone integrableOn
    rw [localBox_iUnion, Measure.restrict_univ] at limit
    have equality : (fun radius => (stage radius).val) = fun radius =>
        ∫ point in localBox radius, localIntegrand data parameter (extension parameter)
          (flat.1 parameter) argument point ∂localRadicalMeasure := funext stageHilbert
    rw [equality]
    exact limit
  -- the sup norm limit
  have tailLimit : Tendsto (fun radius => ∫ point in (localBox radius)ᶜ,
      hcMajorant degree parameter.re constant point ∂localRadicalMeasure) atTop (𝓝 0) := by
    have majorantOn : IntegrableOn (hcMajorant degree parameter.re constant)
        (⋃ radius, localBox radius) localRadicalMeasure := by
      rw [localBox_iUnion]
      exact integrableOn_univ.mpr majorantIntegrable
    have limit := tendsto_setIntegral_of_monotone localBox_measurable localBox_monotone majorantOn
    rw [localBox_iUnion, Measure.restrict_univ] at limit
    have constantLimit : Tendsto (fun _ : ℕ => ∫ point,
        hcMajorant degree parameter.re constant point ∂localRadicalMeasure) atTop
        (𝓝 (∫ point, hcMajorant degree parameter.re constant point ∂localRadicalMeasure)) :=
      tendsto_const_nhds
    have difference := constantLimit.sub limit
    simp only [sub_self] at difference
    have equality : (fun radius => ∫ point in (localBox radius)ᶜ,
        hcMajorant degree parameter.re constant point ∂localRadicalMeasure) = fun radius =>
        (∫ point, hcMajorant degree parameter.re constant point ∂localRadicalMeasure) -
          ∫ point in localBox radius, hcMajorant degree parameter.re constant point
            ∂localRadicalMeasure := by
      funext radius
      have split := integral_add_compl (localBox_measurable radius) majorantIntegrable
      rw [← split]
      ring
    rw [equality]
    exact difference
  have scalarLimit : Tendsto (fun radius => boundedRealization data.cusp (stage radius)) atTop
      (𝓝 target) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun radius => norm_nonneg _) (fun radius => ?_) tailLimit
    show ‖boundedRealization data.cusp (stage radius) - target‖ ≤ _
    refine lp.norm_le_of_forall_le' _ (fun test => ?_)
    rw [lp.coeFn_sub, Pi.sub_apply, targetApply]
    change ‖data.cusp.realize (stage radius) test - ∫ coordinates, localScalarIntegrand data
      parameter (extension parameter) (flat.1 parameter) argument test coordinates
        ∂localRadicalMeasure‖ ≤ _
    rw [stageScalar radius test]
    have split := integral_add_compl (localBox_measurable radius) (scalarIntegrable test)
    have difference : (∫ point in localBox radius, localScalarIntegrand data parameter
        (extension parameter) (flat.1 parameter) argument test point ∂localRadicalMeasure) -
        ∫ point, localScalarIntegrand data parameter (extension parameter) (flat.1 parameter)
          argument test point ∂localRadicalMeasure =
        -∫ point in (localBox radius)ᶜ, localScalarIntegrand data parameter (extension parameter)
          (flat.1 parameter) argument test point ∂localRadicalMeasure := by
      rw [← split]
      ring
    rw [difference, norm_neg]
    exact norm_integral_le_of_norm_le majorantIntegrable.integrableOn
      (Filter.Eventually.of_forall (fun coordinates => pointwise test coordinates))
  -- fixedness of the limits
  have vectorFixed : (localValue data parameter (extension parameter) (flat.1 parameter) argument) ∈
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace
        data.cusp
        TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence := by
    intro unit
    exact localValue_fixed data parameter (extension parameter) (flat.1 parameter) argument
      ⟨unit.val, principal_le_level_of_integral argument integral unit.property⟩
  have targetFixed : ∀ unit :
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence,
      ∀ point : BinaryAdelicGL, target (point * atFinite unit.val) = target point := by
    intro unit point
    have unitLevel : unit.val ∈ LineOrbitLevel.level argument :=
      principal_le_level_of_integral argument integral unit.property
    obtain ⟨levelElement, translation⟩ := LineOrbitLevel.level_translate argument
      ⟨unit.val, unitLevel⟩
    obtain ⟨integralUnit, _, equality⟩ := unit.property
    rw [targetApply, targetApply]
    exact localScalarIntegral_fixed data parameter (extension parameter) (flat.1 parameter)
      argument unit.val ⟨integralUnit, equality⟩
      (LineOrbitLevel.level_det_norm_one argument ⟨unit.val, unitLevel⟩) levelElement
      translation point
  have equality := FixedRealizationLimit.principal_limit_unique atTop data stage
    ⟨localValue data parameter (extension parameter) (flat.1 parameter) argument,
      localValue_mem_smooth data parameter (extension parameter) (flat.1 parameter) halfPlane
        argument integral⟩ vectorFixed target targetFixed hilbertLimit scalarLimit
  rw [← targetApply binary]
  exact (congrArg (fun value : lp (fun _ : BinaryAdelicGL => ℂ) ⊤ => value binary) equality).symm

end TernaryPeriodPolynomials.EdgeConvergence
