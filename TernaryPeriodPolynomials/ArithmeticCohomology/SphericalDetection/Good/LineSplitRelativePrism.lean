module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneNormalizedValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstTransition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourceSplitRelativeVertexPrimitive_goodLine_mixed {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    let normalized := splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative
    sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))) (atInfinity real) -
      sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix)) (atInfinity real) =
    (sourceRelativeProjectedValue data normalized projection real
        (goodLineRealVertices (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))) -
      sourceRelativeProjectedValue data normalized projection real
        (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix))) +
      goodLineCuspidalMixedPrimitiveValue data.cusp
        (sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection real) matrix radical := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly degree)).addCommGroup
  dsimp only
  rw [sourceSplitRelativeVertexPrimitive_differential data source cocycle primitive relative formula,
    sourceSplitRelativeVertexPrimitive_differential data source cocycle primitive relative formula]
  apply Subtype.ext
  funext argument
  have differential := goodLineRealMixedPrimitiveValue_differential
    (fun vertices => (sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection real vertices).val argument)
    matrix radical
  simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply,
    goodLineCuspidalMixedPrimitiveValue, goodLineRealMixedPrimitiveValue] at differential ⊢
  linear_combination (norm := abel) differential

theorem goodLineMixedCuspidalValues_split_relative_prism {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCuspidalValues data source cocycle matrix (atInfinity real) =
      goodLineRelativeMixedProjectedValue data
          (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative)
          projection real matrix +
        goodLineCuspidalPrimitiveCoordinate data.cusp
          (sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection real) matrix := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (Binary.HomogeneousPoly (degree + 1))) :=
    (cuspidalTensorValues data.cusp (Binary.HomogeneousPoly (degree + 1))).addCommGroup
  rw [goodLineMixedCuspidalValues,
    sourceSplitRelativeVertexPrimitive_goodLine_mixed data source cocycle primitive relative formula,
    sourceSplitRelativeVertexPrimitive_goodLine_mixed data source cocycle primitive relative formula]
  simp only [goodLineRelativeMixedProjectedValue, goodLineCuspidalPrimitiveCoordinate, map_add]
  abel

theorem goodLineCuspidalArchimedeanIntegral_split_relative_prism {degree : ℕ} (data : InducingData degree)
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
        functional ((goodLineRelativeMixedProjectedValue data
            (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative)
            projection (standardGoodLineRealArgument real) matrix +
          goodLineCuspidalPrimitiveCoordinate data.cusp
            (sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection
              (standardGoodLineRealArgument real)) matrix).val
                (atFinite (standardGoodLineFiniteCoordinates finite).block))
        ∂((volume : Measure ℝ).prod volume) := by
  apply integral_congr_ae
  filter_upwards [] with real
  rw [← goodLineMixedCuspidalValues_split_relative_prism data source cocycle primitive relative formula projection]
  rw [goodLineMixedCuspidalValues_apply]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
