module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.FlagHeight
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentCompactDomain
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RightHalfPlane
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.Integral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentCompactDomain
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatConstantTerm

theorem exists_majorant {degree : ℕ} {data : InducingData degree}
    {sectionFunction : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data sectionFunction)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) (point : AdelicGL) :
    ∃ majorant : Flags .plane → ℝ, Summable majorant ∧
      ∀ pair ∈ closureBox ×ˢ closureBox, ∀ flag,
        ‖term sectionFunction parameter point flag pair‖ ≤ majorant flag := by
  let exponent : ℝ := parameter.re + ((degree : ℝ) + 6) / 2
  have exponentBound : 3 < exponent := by dsimp [exponent]; linarith
  have exponentNonnegative : 0 ≤ exponent := by linarith
  obtain ⟨cuspBound, cuspNonnegative, cuspBounded⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar.maximalCompact_bound (flat.1 cohomologicalPoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes.continuousStages_of_finite_types data.cusp
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.EndpointAdmissibility.all_finiteDimensional data))
  let points := (fun pair : Adeles × Adeles => planeUnipotent pair.1 pair.2 * point) '' (closureBox ×ˢ closureBox)
  have compact : IsCompact points := (closureBox_compact.prod closureBox_compact).image
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneChartContinuity.planeUnipotent_continuous.mul continuous_const)
  obtain ⟨heightBound, heightBounded⟩ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFlagHeight.height_bound points compact
  let constant : ℝ := ((degree : ℝ) + 3) / 3 * Real.log (adeleNorm (GeneralLinearGroup.det point) : ℝ)
  refine ⟨fun flag => flagRadius flag ^ (-exponent) * (Real.exp (constant + exponent * heightBound) * cuspBound),
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.summable_integralFlagRow_rpow (-exponent) (by linarith)).mul_right _, ?_⟩
  intro pair membership flag
  have bound := TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalScalar.height_bound_of_compact_bound flat cuspBound cuspBounded parameter
    (rationalGroup flag.out⁻¹ * (planeUnipotent pair.1 pair.2 * point))
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalBounds.adeleNorm_det_rational_mul] at bound
  simp only [map_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral.det_planeUnipotent, one_mul] at bound
  have heightInequality := heightBounded _ ⟨pair, membership, rfl⟩ flag
  calc
    ‖term sectionFunction parameter point flag pair‖ ≤
        Real.exp (constant + exponent * TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight.height
          (rationalGroup flag.out⁻¹ * (planeUnipotent pair.1 pair.2 * point))) * cuspBound := bound
    _ ≤ Real.exp (constant + exponent * (heightBound - Real.log (flagRadius flag))) * cuspBound := by
      apply mul_le_mul_of_nonneg_right _ cuspNonnegative
      exact Real.exp_le_exp.mpr (add_le_add_right
        (mul_le_mul_of_nonneg_left heightInequality exponentNonnegative) constant)
    _ = _ := by
      dsimp only
      rw [Real.rpow_def_of_pos (flagRadius_pos flag), ← mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem average_literalSum {degree : ℕ} {data : InducingData degree}
    {sectionFunction : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data sectionFunction)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) (point : AdelicGL) :
    average (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFunction parameter) point = sectionFunction parameter point := by
  obtain ⟨majorant, summable, bounded⟩ := exists_majorant flat parameter rightHalfPlane point
  exact UnipotentCompactDomain.average_of_majorant (flat.1 parameter) point majorant summable
    (fun pair membership flag => bounded pair ⟨domain_subset membership.1, domain_subset membership.2⟩ flag)

theorem literalSum_integrable {degree : ℕ} {data : InducingData degree}
    {sectionFunction : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data sectionFunction)
    (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) (point : AdelicGL) :
    Integrable (fun pair : Adeles × Adeles =>
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFunction parameter (planeUnipotent pair.1 pair.2 * point))
      parameterMeasure := by
  obtain ⟨majorant, summable, bounded⟩ := exists_majorant flat parameter rightHalfPlane point
  apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.SeriesIntegrability.tsum_integrable
    (fun flag => term sectionFunction parameter point flag) (term_integrable (flat.1 parameter) point)
  apply summable.of_nonneg_of_le (fun flag => integral_nonneg (fun pair => norm_nonneg _))
  intro flag
  have boundIntegral := integral_mono_ae (term_integrable (flat.1 parameter) point flag).norm
    (integrable_const (μ := parameterMeasure) (majorant flag))
    (ae_mem_domain.mono (fun pair membership => bounded pair ⟨domain_subset membership.1, domain_subset membership.2⟩ flag))
  simpa only [integral_const, probReal_univ, one_smul] using boundIntegral

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatConstantTerm
