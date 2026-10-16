module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.LocalThreeEntry.Helpers

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.LocalThreeBadPlaneEntry

theorem local_three_bad_plane_entry : LocalBadPlaneEntry := by
  intro measure haar normalized sectionValue support invariant
  let : measure.IsAddHaarMeasure := haar
  rw [Helpers.integrand_indicator sectionValue support invariant]
  have measurable : MeasurableSet (Helpers.smallBall ×ˢ Helpers.smallBall) := by
    have small_measurable : MeasurableSet Helpers.smallBall :=
      (isOpen_lt continuous_norm continuous_const).measurableSet
    exact small_measurable.prod small_measurable
  have volume : (measure.prod measure) (Helpers.smallBall ×ˢ Helpers.smallBall) =
      (1 / 9 : ENNReal) := by
    rw [MeasureTheory.Measure.prod_prod, Helpers.smallBall_measure measure normalized]
    rw [one_div, one_div, ← ENNReal.mul_inv (by left; norm_num) (by right; norm_num)]
    norm_num
  constructor
  · apply (MeasureTheory.integrable_indicator_iff measurable).mpr
    exact MeasureTheory.integrableOn_const (by rw [volume]; norm_num) enorm_ne_top
  · rw [MeasureTheory.integral_indicator_const _ measurable]
    change ((measure.prod measure) (Helpers.smallBall ×ˢ Helpers.smallBall)).toReal •
      sectionValue 1 = _
    rw [volume]
    norm_num [Complex.real_smul]


end TernaryPeriodPolynomials.LocalThreeBadPlaneEntry
