module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.ParabolicLocalRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLocalCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneRelative_mixed_analyticAt_one {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneNormalizedGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive)) (radical : RealPlaneRadical) :
    AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      cuspidalTensorHilbertEmbedding data.cusp basis
        (relative.val (SemidirectProduct.inr (invertibleMatrix matrix),
          SemidirectProduct.inl (realRadicalInverseLevi (invertibleMatrix matrix) radical))).val -
      cuspidalTensorHilbertEmbedding data.cusp basis
        (relative.val (SemidirectProduct.inl radical, SemidirectProduct.inr (invertibleMatrix matrix))).val) 1 := by
  have unit_zero := realPlaneRelative_primitive_unit _ _
    (sourcePlaneNormalizedGroupCocycle_unit data source cocycle) primitive relative formula
  have first_regular := sourcePlaneNormalizedGroupCocycle_hilbertContDiffAt data basis source cocycle
    (fun matrix : BinaryRealMatrix => SemidirectProduct.inr (invertibleMatrix matrix))
    (fun matrix : BinaryRealMatrix => SemidirectProduct.inl (realRadicalInverseLevi (invertibleMatrix matrix) radical))
    1 realPlaneLeviMatrix_contDiffAt_one (realPlaneInverseRadicalMatrix_contDiffAt_one radical)
  have second_regular := sourcePlaneNormalizedGroupCocycle_hilbertContDiffAt data basis source cocycle
    (fun _ : BinaryRealMatrix => SemidirectProduct.inl radical)
    (fun matrix : BinaryRealMatrix => SemidirectProduct.inr (invertibleMatrix matrix))
    1 contDiffAt_const realPlaneLeviMatrix_contDiffAt_one
  have action := realPlaneLeviAction_orbital_analyticAt_of_trivial degree data.cusp data.chi trivial basis
    (fun point : Fin 2 → ℝ => (primitive (Multiplicative.ofAdd point)).val)
    (realRadicalInverseLevi (invertibleMatrix (1 : BinaryRealMatrix)) radical).toAdd (analytic _)
  have input_analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      (matrix, (realRadicalInverseLevi (invertibleMatrix matrix) radical).toAdd)) 1 :=
    analyticAt_id.prod (realRadicalInverseLevi_matrix_contDiffAt_one radical).analyticAt
  have action_analytic := action.comp (f := fun matrix : BinaryRealMatrix =>
    (matrix, (realRadicalInverseLevi (invertibleMatrix matrix) radical).toAdd)) (x := 1) input_analytic
  have primitive_analytic : AnalyticAt ℝ (fun _ : BinaryRealMatrix =>
      cuspidalTensorHilbertEmbedding data.cusp basis (primitive radical).val) 1 := analyticAt_const
  convert ((first_regular.analyticAt.sub second_regular.analyticAt).sub action_analytic).add primitive_analytic using 1
  funext matrix
  let embedding : realPlaneLevelCuspidalRep degree data.cusp data.chi →ₗ[ℂ] (index → data.cusp.H) :=
    (cuspidalTensorHilbertEmbedding data.cusp basis).comp
      (cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree)).subtype
  have equality := congrArg embedding (realPlaneRelative_mixed_formula _ _ primitive unit_zero relative formula (invertibleMatrix matrix) radical)
  simp only [map_sub, map_add] at equality
  exact equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
