module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstHalfPlane
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineHalfPlaneCoordinateMap (point : ℝ × ℝ) : ℝ × ℝ :=
  (-point.1 / point.2, (point.1 ^ 2 + point.2 ^ 2) / point.2)

def goodLineHalfPlaneCoordinateDerivative (point : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![-1 / point.2, point.1 / point.2 ^ 2;
        2 * point.1 / point.2, 1 - point.1 ^ 2 / point.2 ^ 2])

theorem goodLineHalfPlaneCoordinateMap_hasFDerivAt (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    HasFDerivAt goodLineHalfPlaneCoordinateMap (goodLineHalfPlaneCoordinateDerivative point) point := by
  have first : HasFDerivAt (fun input : ℝ × ℝ => input.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) point := hasFDerivAt_fst
  have second : HasFDerivAt (fun input : ℝ × ℝ => input.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) point := hasFDerivAt_snd
  have inverse := (hasDerivAt_inv pivot).comp_hasFDerivAt point second
  have derivative := (first.neg.fun_mul inverse).prodMk
    (((first.fun_mul first).add (second.fun_mul second)).fun_mul inverse)
  convert derivative using 1
  · funext input
    simp [goodLineHalfPlaneCoordinateMap, div_eq_mul_inv, pow_two]
  · ext <;>
      simp [goodLineHalfPlaneCoordinateDerivative, Matrix.toLin_finTwoProd,
        ContinuousLinearMap.prod_apply] <;>
      field_simp <;> ring

theorem goodLineHalfPlaneCoordinateDerivative_det (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    (goodLineHalfPlaneCoordinateDerivative point).det = -(point.1 ^ 2 + point.2 ^ 2) / point.2 ^ 3 := by
  change LinearMap.det (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      !![-1 / point.2, point.1 / point.2 ^ 2;
        2 * point.1 / point.2, 1 - point.1 ^ 2 / point.2 ^ 2]) = _
  rw [LinearMap.det_toLin, Matrix.det_fin_two]
  change (-1 / point.2) * (1 - point.1 ^ 2 / point.2 ^ 2) -
    point.1 / point.2 ^ 2 * (2 * point.1 / point.2) = _
  field_simp
  ring

theorem goodLineHalfPlaneCoordinateDerivative_abs_det (point : ℝ × ℝ) (positive : 0 < point.2) :
    |(goodLineHalfPlaneCoordinateDerivative point).det| = (point.1 ^ 2 + point.2 ^ 2) / point.2 ^ 3 := by
  rw [goodLineHalfPlaneCoordinateDerivative_det point (ne_of_gt positive), neg_div, abs_neg,
    abs_of_nonneg (by positivity)]

theorem goodLineHalfPlaneCoordinateMap_eq (point : UpperHalfPlane) :
    goodLineHalfPlaneCoordinateMap (point.re, point.im) = goodLineHalfPlaneCoordinates point := by
  simp [goodLineHalfPlaneCoordinateMap, goodLineHalfPlaneCoordinates, Complex.normSq_apply, pow_two]

theorem goodLineHalfPlaneCoordinateMap_kernel_base (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    1 + (goodLineHalfPlaneCoordinateMap point).1 ^ 2 + (goodLineHalfPlaneCoordinateMap point).2 ^ 2 =
      (point.1 ^ 2 + point.2 ^ 2) * (1 + point.1 ^ 2 + point.2 ^ 2) / point.2 ^ 2 := by
  simp only [goodLineHalfPlaneCoordinateMap]
  field_simp
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
