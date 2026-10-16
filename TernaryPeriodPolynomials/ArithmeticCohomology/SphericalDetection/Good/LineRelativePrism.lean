module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RelativeVertexPrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstProjectionRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineRelativeMixedProjectedValue {degree : ℕ} (data : InducingData degree)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    cuspidalTensorValues data.cusp (Binary.HomogeneousPoly (degree + 1)) :=
  let mixed (radical : RadicalLattice) :=
    sourceRelativeProjectedValue data relative projection real
        (goodLineRealVertices (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))) -
      sourceRelativeProjectedValue data relative projection real
        (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix))
  cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 0) (mixed radicalLatticeFirst) +
    cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 1) (mixed radicalLatticeSecond)

def goodLineCuspidalPrimitiveCoordinate {degree : ℕ} (cusp : CuspidalRepresentation)
    (primitive : (Fin 2 → RealGL3) → cuspidalTensorValues cusp (HomogeneousPoly degree))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) :=
  cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 0)
      (goodLineCuspidalMixedPrimitiveValue cusp primitive matrix radicalLatticeFirst) +
    cuspidalTensorMap cusp (lowerRadicalLatticeContribution degree 1)
      (goodLineCuspidalMixedPrimitiveValue cusp primitive matrix radicalLatticeSecond)

theorem goodLineMixedCuspidalValues_relative_prism {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCuspidalValues data source cocycle matrix (atInfinity real) =
      goodLineRelativeMixedProjectedValue data relative projection real matrix +
        goodLineCuspidalPrimitiveCoordinate data.cusp
          (sourceRelativeVertexPrimitive data source cocycle primitive projection real) matrix := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (Binary.HomogeneousPoly (degree + 1))) :=
    (cuspidalTensorValues data.cusp (Binary.HomogeneousPoly (degree + 1))).addCommGroup
  rw [goodLineMixedCuspidalValues,
    sourceRelativeVertexPrimitive_goodLine_mixed data source cocycle primitive relative formula,
    sourceRelativeVertexPrimitive_goodLine_mixed data source cocycle primitive relative formula]
  simp only [goodLineRelativeMixedProjectedValue, goodLineCuspidalPrimitiveCoordinate, map_add]
  abel

/-- The actual scalar integral retains both the relative value and its corrected prism together. -/
theorem goodLineCuspidalArchimedeanIntegral_relative_prism {degree : ℕ} (data : InducingData degree)
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
      ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
        functional ((goodLineRelativeMixedProjectedValue data relative projection
            (standardGoodLineRealArgument real) matrix +
          goodLineCuspidalPrimitiveCoordinate data.cusp
            (sourceRelativeVertexPrimitive data source cocycle primitive projection
              (standardGoodLineRealArgument real)) matrix).val
                (atFinite (standardGoodLineFiniteCoordinates finite).block))
        ∂((volume : Measure ℝ).prod volume) := by
  apply integral_congr_ae
  filter_upwards [] with real
  rw [← goodLineMixedCuspidalValues_relative_prism data source cocycle primitive relative formula projection]
  rw [goodLineMixedCuspidalValues_apply]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
