module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePlaneIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineSplitRelativePrism

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLinePlaneCoordinateKernel (parameter : ℂ) (point : ℝ × ℝ) : ℂ :=
  (((point.1 ^ 2 + point.2 ^ 2) / |point.2| ^ 3 : ℝ) : ℂ) *
    Complex.exp ((-(3 : ℂ) / 4 - parameter / 2) *
      (Real.log ((point.1 ^ 2 + point.2 ^ 2) * (1 + point.1 ^ 2 + point.2 ^ 2) / point.2 ^ 2) : ℂ))

theorem goodLinePlaneCoordinateKernel_eq (parameter : ℂ) (point : ℝ × ℝ) (pivot : point.2 ≠ 0) :
    goodLinePlaneCoordinateKernel parameter point =
      (((point.1 ^ 2 + point.2 ^ 2) / |point.2| ^ 3 : ℝ) : ℂ) *
        standardGoodLineRealKernel parameter (goodLineHalfPlaneCoordinateMap point) := by
  rw [standardGoodLineRealKernel, goodLineHalfPlaneCoordinateMap_kernel_base point pivot]
  rfl

theorem goodLinePlaneCoordinateKernel_endpoint (point : ℝ × ℝ) :
    goodLinePlaneCoordinateKernel cohomologicalPoint point =
      (((point.1 ^ 2 + point.2 ^ 2) / |point.2| ^ 3 : ℝ) : ℂ) := by
  norm_num [goodLinePlaneCoordinateKernel, cohomologicalPoint]

theorem goodLineCuspidalArchimedeanIntegral_plane_coordinates {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineCuspidalArchimedeanIntegral data source cocycle parameter matrix functional finite =
      ∫ point : ℝ × ℝ, goodLinePlaneCoordinateKernel parameter point *
        functional ((goodLineMixedCuspidalValues data source cocycle matrix
          (atInfinity (standardGoodLineRealArgument (goodLineHalfPlaneCoordinateMap point)))).val
            (atFinite (standardGoodLineFiniteCoordinates finite).block))
        ∂((volume : Measure ℝ).prod volume) := by
  rw [goodLineCuspidalArchimedeanIntegral, integral_goodLinePlaneCoordinateMap]
  apply integral_congr_ae
  filter_upwards [goodLinePlane_second_ne_zero_ae] with point pivot
  rw [goodLinePlaneCoordinateKernel_eq parameter point pivot, goodLineMixedCuspidalValues_apply]
  change (((point.1 ^ 2 + point.2 ^ 2) / |point.2| ^ 3 : ℝ) : ℂ) *
      (standardGoodLineRealKernel parameter (goodLineHalfPlaneCoordinateMap point) * _) = _
  rw [mul_assoc]

theorem goodLineCuspidalArchimedeanIntegral_split_plane_coordinates {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (projection : RealGL3 → RealPlaneGroup) (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineCuspidalArchimedeanIntegral data source cocycle parameter matrix functional finite =
      ∫ point : ℝ × ℝ, goodLinePlaneCoordinateKernel parameter point *
        functional ((goodLineRelativeMixedProjectedValue data
            (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative)
            projection (standardGoodLineRealArgument (goodLineHalfPlaneCoordinateMap point)) matrix +
          goodLineCuspidalPrimitiveCoordinate data.cusp
            (sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection
              (standardGoodLineRealArgument (goodLineHalfPlaneCoordinateMap point))) matrix).val
                (atFinite (standardGoodLineFiniteCoordinates finite).block))
        ∂((volume : Measure ℝ).prod volume) := by
  rw [goodLineCuspidalArchimedeanIntegral_plane_coordinates]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [goodLineMixedCuspidalValues_split_relative_prism data source cocycle primitive relative formula projection]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
