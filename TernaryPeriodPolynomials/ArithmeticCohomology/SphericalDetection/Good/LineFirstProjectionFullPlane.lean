module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstProjectionLevi

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFirstProjection_fraction (real : ℝ × ℝ) (pivot : real.2 ≠ 0) :
    UpperHalfPlane.num (realPlaneFirstProjection (standardGoodLineRealArgument real)).right Complex.I /
        UpperHalfPlane.denom (realPlaneFirstProjection (standardGoodLineRealArgument real)).right Complex.I =
      -(real.2 : ℂ) / ((real.1 : ℂ) + Complex.I) := by
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, goodLineFirstProjection_binary real pivot]
  change ((0 : ℂ) * Complex.I + 1) /
    (((-(1 : ℝ) / real.2 : ℝ) : ℂ) * Complex.I + ((-real.1 / real.2 : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, zero_mul, zero_add]
  have denominator : -(1 : ℂ) / (real.2 : ℂ) * Complex.I +
      -(real.1 : ℂ) / (real.2 : ℂ) = -(((real.1 : ℂ) + Complex.I) / (real.2 : ℂ)) := by ring
  rw [denominator, one_div, inv_neg, inv_div, neg_div]

theorem goodLineFirstProjection_fullPlane_coordinates (real : ℝ × ℝ) (pivot : real.2 ≠ 0) :
    let point := (realPlaneFirstProjection (standardGoodLineRealArgument real)).right • UpperHalfPlane.I
    point.re = (goodLineFirstCoordinateMap real).1 ∧
      point.im = |(goodLineFirstCoordinateMap real).2| := by
  dsimp only
  rw [UpperHalfPlane.re_smul, UpperHalfPlane.im_smul, UpperHalfPlane.coe_I,
    goodLineFirstProjection_fraction real pivot]
  constructor
  · simp [goodLineFirstCoordinateMap, Complex.div_re, Complex.normSq_apply, pow_two]
  · apply congrArg abs
    simp [goodLineFirstCoordinateMap, Complex.div_im, Complex.normSq_apply, pow_two]
    ring

def goodLinePlanePoint (point : ℝ × ℝ) (pivot : point.2 ≠ 0) : UpperHalfPlane :=
  ⟨(point.1 : ℂ) + ((|point.2| : ℝ) : ℂ) * Complex.I, by simpa using abs_pos.mpr pivot⟩

theorem goodLineFirstProjection_planePoint (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    (realPlaneFirstProjection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinateMap point))).right •
        UpperHalfPlane.I = goodLinePlanePoint point pivot := by
  have mapped_pivot := goodLineHalfPlaneCoordinateMap_bijOn_nonzero.mapsTo pivot
  have coordinates := goodLineFirstProjection_fullPlane_coordinates (goodLineHalfPlaneCoordinateMap point) mapped_pivot
  simp only [goodLineHalfPlaneCoordinateMap_inverse point pivot] at coordinates
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change ((realPlaneFirstProjection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinateMap point))).right •
        UpperHalfPlane.I).re = _
    simpa [goodLinePlanePoint] using coordinates.1
  · change ((realPlaneFirstProjection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinateMap point))).right •
        UpperHalfPlane.I).im = _
    simpa [goodLinePlanePoint] using coordinates.2

theorem goodLineFirstProjection_planePoint_coe (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    (↑((realPlaneFirstProjection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinateMap point))).right •
        UpperHalfPlane.I) : ℂ) = (point.1 : ℂ) + ((|point.2| : ℝ) : ℂ) * Complex.I := by
  rw [goodLineFirstProjection_planePoint point pivot]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
