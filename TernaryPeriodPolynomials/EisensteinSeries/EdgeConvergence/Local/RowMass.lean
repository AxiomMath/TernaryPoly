module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Majorant
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Ball
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeMeasure

@[expose] public section


/-!
# The finite row mass of the local standard argument

The row lattice of the finite local standard argument is the product of the closed ball of radius
`max 1 (max |u₁|₃ |u₂|₃)` in `ℚ₃` and the integral lattice away from `3`. Its Haar mass is therefore
comparable to the `3`-adic part of the local height.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

local instance normalizedLocalThreeMeasure_isAddHaarMeasure' :
    normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

/-- The finite row mass of the local standard argument is the mass of a ball in `ℚ₃`. -/
theorem rowMass_local (first second : ℚ_[3]) :
    rowMass ((weyl⁻¹ : FiniteGL) *
        lineUnipotent (finiteAtThreeScalar first) (finiteAtThreeScalar second)) =
      normalizedLocalThreeMeasure.real
        {value : ℚ_[3] | ‖value‖ ≤ max 1 (max ‖first‖ ‖second‖)} := by
  unfold rowMass Measure.real
  rw [← finiteThreeSplit_symm_measurePreserving.measure_preimage
    (rowLattice_open _).measurableSet.nullMeasurableSet, localRowLattice, Measure.prod_prod,
    finiteAwayThreeMeasure_normalized, mul_one]

/-- The finite row mass of the local standard argument is at least a third of the `3`-adic local
height. -/
theorem rowMass_local_ge (first second : ℚ_[3]) :
    max 1 (max ‖first‖ ‖second‖) / 3 ≤
      rowMass ((weyl⁻¹ : FiniteGL) *
        lineUnipotent (finiteAtThreeScalar first) (finiteAtThreeScalar second)) := by
  rw [rowMass_local]
  exact (localBall_real_bounds _ (le_max_left _ _)).1

/-- The finite row mass of the local standard argument is at most three times the `3`-adic local
height. -/
theorem rowMass_local_le (first second : ℚ_[3]) :
    rowMass ((weyl⁻¹ : FiniteGL) *
        lineUnipotent (finiteAtThreeScalar first) (finiteAtThreeScalar second)) ≤
      3 * max 1 (max ‖first‖ ‖second‖) := by
  rw [rowMass_local]
  exact (localBall_real_bounds _ (le_max_left _ _)).2

end TernaryPeriodPolynomials.EdgeConvergence
