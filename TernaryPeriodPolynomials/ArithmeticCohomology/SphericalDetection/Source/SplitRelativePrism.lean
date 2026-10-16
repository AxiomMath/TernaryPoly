module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRelativePrism
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneSplitNormalization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourceSplitRelativeVertexPrimitive {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (vertices : Fin 2 → RealGL3) :
    cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
  sourceRelativeVertexPrimitive data source cocycle primitive projection real vertices -
    cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
      (groupHomogeneousOneValue (realPlaneLevelCuspidalRep degree data.cusp data.chi)
        (splitMixedPrimitive realPlaneSplitting (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative)
        (fun index => projection (real * vertices index))).val

theorem sourceSplitRelativeVertexPrimitive_differential {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (projection : RealGL3 → RealPlaneGroup) (real : RealGL3) (vertices : Fin 3 → RealGL3) :
    sourcePlaneCuspidalValues data source cocycle vertices (atInfinity real) =
      sourceRelativeProjectedValue data
          (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree data.cusp data.chi) relative)
          projection real vertices +
        (sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection real ![vertices 1, vertices 2] -
          sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection real ![vertices 0, vertices 2] +
          sourceSplitRelativeVertexPrimitive data source cocycle primitive relative projection real ![vertices 0, vertices 1]) := by
  let : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly degree)).addCommGroup
  let representation := realPlaneLevelCuspidalRep degree data.cusp data.chi
  let points (index : Fin 3) := projection (real * vertices index)
  let correction := splitMixedPrimitive realPlaneSplitting representation relative
  have normalized : groupHomogeneousTwoValue representation
        (splitMixedNormalize realPlaneSplitting representation relative).val points =
      groupHomogeneousTwoValue representation relative.val points +
        groupHomogeneousTwoValue representation (twoBoundaryCycle representation correction) points := by
    change representation.ρ (points 0)
        (relative.val ((points 0)⁻¹ * points 1, (points 1)⁻¹ * points 2) +
          twoBoundaryCycle representation correction ((points 0)⁻¹ * points 1, (points 1)⁻¹ * points 2)) = _
    rw [map_add]
    rfl
  rw [groupHomogeneousTwoValue_boundary] at normalized
  let linear : representation →ₗ[ℂ] cuspidalTensorValues data.cusp (HomogeneousPoly degree) :=
    (cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)).comp
      (cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree)).subtype
  have mapped := congrArg linear normalized
  simp only [map_add, map_sub] at mapped
  dsimp only [linear, LinearMap.comp_apply, Submodule.subtype_apply, representation, correction, points] at mapped
  change cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
      (groupHomogeneousTwoValue representation
        (splitMixedNormalize realPlaneSplitting representation relative).val points).val =
    cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
      (groupHomogeneousTwoValue representation relative.val points).val +
      (cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
        (groupHomogeneousOneValue representation correction ![points 1, points 2]).val -
      cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
        (groupHomogeneousOneValue representation correction ![points 0, points 2]).val +
      cuspidalTensorMap data.cusp (realCoefficientComponent degree data.chi real⁻¹)
        (groupHomogeneousOneValue representation correction ![points 0, points 1]).val) at mapped
  have original := sourceRelativeVertexPrimitive_differential data source cocycle primitive relative formula
    projection real vertices
  have pair (first second : RealGL3) :
      (fun index : Fin 2 => projection (real * ![first, second] index)) =
        ![projection (real * first), projection (real * second)] := by
    funext index
    fin_cases index <;> rfl
  simp only [sourceSplitRelativeVertexPrimitive, sourceRelativeProjectedValue, pair]
  simp only [sourceRelativeProjectedValue] at original
  linear_combination (norm := abel) original - mapped

end TernaryPeriodPolynomials.SphericalDetection.Helpers
