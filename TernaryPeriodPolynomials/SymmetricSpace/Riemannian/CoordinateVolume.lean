module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Density
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.SetTheory.Cardinal.ENNReal

@[expose] public section

/-! Local coordinate volumes agree under the actual arithmetic quotient chart changes. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open MeasureTheory Set SymmetricSpacePositive SymmetricSpaceCharts
open SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ENNReal ContDiff

/-- Lebesgue measure weighted by the genuine trace-metric Gram determinant. -/
def coordinateVolume : Measure Coordinates :=
  volume.withDensity (fun x => ENNReal.ofReal (coordinateDensity x))

theorem coordinateVolume_apply (s : Set Coordinates) :
    coordinateVolume s = ∫⁻ x in s, ENNReal.ofReal (coordinateDensity x) :=
  withDensity_apply' _ _

/-- Every measurable subset of an actual chart overlap has the same local Riemannian volume
in both coordinate systems. -/
theorem coordinateVolume_quotientChart_image (S T : Space) {s : Set Coordinates}
    (hs : MeasurableSet s) (hsub : s ⊆ ((quotientChart S).symm.trans (quotientChart T)).source) :
    coordinateVolume (((quotientChart S).symm.trans (quotientChart T)) '' s) =
      coordinateVolume s := by
  let e := (quotientChart S).symm.trans (quotientChart T)
  have hd (x : Coordinates) (hx : x ∈ s) : HasFDerivWithinAt e (fderiv ℝ e x) s x := by
    have h := ((quotientChart_transition_contDiffOn S T).differentiableOn (by simp) x (hsub hx)).differentiableAt
      (e.open_source.mem_nhds (hsub hx))
    exact h.hasFDerivAt.hasFDerivWithinAt
  rw [coordinateVolume_apply, coordinateVolume_apply,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hd (e.injOn.mono hsub)]
  apply setLIntegral_congr_fun hs
  intro x hx
  have h := coordinateDensity_quotientChart S T x (hsub hx)
  change ENNReal.ofReal |(fderiv ℝ e x).det| * ENNReal.ofReal (coordinateDensity (e x)) =
    ENNReal.ofReal (coordinateDensity x)
  rw [h, ENNReal.ofReal_mul (abs_nonneg _)]

end TernaryPoly.SymmetricSpaceRiemannian
