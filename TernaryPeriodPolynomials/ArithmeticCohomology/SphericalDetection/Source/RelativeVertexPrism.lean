module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.HomogeneousCocycleReconstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFirstProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourceRelativeVertexPrimitive {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (vertices : Fin 2 → RealGL3) :
    cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  sourceCuspidalVertexPrism data source cocycle (fun matrix => realPlaneMatrix (projection matrix)) real 1 vertices +
    cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
      (groupHomogeneousOneValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
        (realPlanePrimitiveExtension _ primitive) (fun index => projection (real * vertices index))).val

def sourceRelativeProjectedValue {degree : ℕ} (data : InducingData degree)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (vertices : Fin 3 → RealGL3) :
    cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
    (groupHomogeneousTwoValue (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative.val
      (fun index => projection (real * vertices index))).val

theorem sourceRelativeVertexPrimitive_differential {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (vertices : Fin 3 → RealGL3) :
    sourcePlaneCuspidalValues data source cocycle vertices (atInfinity real) =
      sourceRelativeProjectedValue data relative projection real vertices +
        (sourceRelativeVertexPrimitive data source cocycle primitive projection real ![vertices 1, vertices 2] -
          sourceRelativeVertexPrimitive data source cocycle primitive projection real ![vertices 0, vertices 2] +
          sourceRelativeVertexPrimitive data source cocycle primitive projection real ![vertices 0, vertices 1]) := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly degree)).addCommGroup
  have prism := sourceCuspidalVertexPrism_differential data source cocycle
    (fun matrix => realPlaneMatrix (projection matrix)) real 1 vertices
  rw [sourceCuspidalRealTranslate_atInfinity] at prism
  have reconstruction := congrArg (cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹))
    (sourcePlaneCuspidalValues_relative_formula data source cocycle primitive relative formula
      (fun index => projection (real * vertices index)))
  have pair (first second : RealGL3) :
      (fun index : Fin 2 => projection (real * ![first, second] index)) =
        ![projection (real * first), projection (real * second)] := by
    funext index
    fin_cases index <;> rfl
  simp only [map_add, map_sub] at reconstruction
  simp only [sourceRelativeVertexPrimitive, sourceRelativeProjectedValue, pair]
  linear_combination (norm := abel) prism + reconstruction

theorem sourceRelativeVertexPrimitive_goodLine_mixed {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))) (atInfinity real) -
      sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix)) (atInfinity real) =
    (sourceRelativeProjectedValue data relative projection real
        (goodLineRealVertices (goodLineLeviSection matrix,
          goodLineRadicalInclusion (lowerLeviLatticeInput matrix radical))) -
      sourceRelativeProjectedValue data relative projection real
        (goodLineRealVertices (goodLineRadicalInclusion radical, goodLineLeviSection matrix))) +
      goodLineCuspidalMixedPrimitiveValue data.cusp
        (sourceRelativeVertexPrimitive data source cocycle primitive projection real) matrix radical := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly degree)).addCommGroup
  rw [sourceRelativeVertexPrimitive_differential data source cocycle primitive relative formula,
    sourceRelativeVertexPrimitive_differential data source cocycle primitive relative formula]
  apply Subtype.ext
  funext argument
  have differential := goodLineRealMixedPrimitiveValue_differential
    (fun vertices => (sourceRelativeVertexPrimitive data source cocycle primitive projection real vertices).val argument)
    matrix radical
  simp only [Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply,
    goodLineCuspidalMixedPrimitiveValue, goodLineRealMixedPrimitiveValue] at differential ⊢
  linear_combination (norm := abel) differential

end TernaryPeriodPolynomials.SphericalDetection.Helpers
