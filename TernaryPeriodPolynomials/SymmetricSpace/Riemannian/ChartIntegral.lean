module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Volume
public import TernaryPeriodPolynomials.Analysis.ChartLocalMeasureIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section


/-! Exact Bochner integration formula in every actual quotient chart. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open MeasureTheory Set SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold
open scoped SymmetricSpaceRiemannian

/-- The actual quotient measure has precisely the constructed coordinate density. -/
theorem orbitVolume_integral_chart (S : Space) (f : OrbitSpace → ℝ) :
    ∫ q in (quotientChart S).source, f q ∂orbitVolume =
      ∫ x in (quotientChart S).target, coordinateDensity x * f ((quotientChart S).symm x) := by
  rw [orbitVolume_restrict_chart, chartVolume, ChartLocalMeasure.integral_localMeasure,
    coordinateVolume, restrict_withDensity (quotientChart S).open_target.measurableSet]
  have hd : AEMeasurable (fun x => ENNReal.ofReal (coordinateDensity x))
      (volume.restrict (quotientChart S).target) :=
    ((contDiffOn_coordinateDensity.continuousOn.mono (quotientChart_target_subset S)).aemeasurable
      (quotientChart S).open_target.measurableSet).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), coordinateDensity, smul_eq_mul]

end TernaryPoly.SymmetricSpaceRiemannian
