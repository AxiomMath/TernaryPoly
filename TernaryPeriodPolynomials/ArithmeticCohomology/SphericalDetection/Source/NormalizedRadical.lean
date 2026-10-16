module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.NormalizedCocycleFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneLevelCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RadicalOrbitalAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def sourcePlaneNormalizedGroupCocycle {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree data.cusp data.chi) :=
  unitNormalizedTwoCocycle _ (sourcePlaneLevelGroupCocycle data source cocycle)

theorem sourcePlaneNormalizedGroupCocycle_unit {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    sourcePlaneNormalizedGroupCocycle data source cocycle (1, 1) = 0 :=
  unitNormalizedTwoCocycle_unit _ _

theorem sourcePlaneNormalizedGroupCocycle_H2 {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    groupCohomology.H2π _ (sourcePlaneNormalizedGroupCocycle data source cocycle) =
      groupCohomology.H2π _ (sourcePlaneLevelGroupCocycle data source cocycle) :=
  unitNormalizedTwoCocycle_H2 _ _

theorem sourcePlaneNormalizedGroupCocycle_hilbert {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (first second : RealPlaneGroup) :
    cuspidalTensorHilbertEmbedding data.cusp basis
        (sourcePlaneNormalizedGroupCocycle data source cocycle (first, second)).val =
      cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneGroupCocycle data source cocycle (first, second)) -
        cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneGroupCocycle data source cocycle (first, 1)) := by
  let embedding : realPlaneLevelCuspidalRep degree data.cusp data.chi →ₗ[ℂ] (index → data.cusp.H) :=
    (cuspidalTensorHilbertEmbedding data.cusp basis).comp
      (cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree)).subtype
  change embedding (unitNormalizedTwoCocycle _ _ (first, second)) = _
  rw [unitNormalizedTwoCocycle_apply, map_sub]
  rfl

theorem sourcePlaneNormalizedGroupCocycle_radical_hilbertContDiff {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ContDiff ℝ ⊤ (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      cuspidalTensorHilbertEmbedding data.cusp basis
        (sourcePlaneNormalizedGroupCocycle data source cocycle
          (SemidirectProduct.inl (Multiplicative.ofAdd point.1),
            SemidirectProduct.inl (Multiplicative.ofAdd point.2))).val) := by
  have regular := sourcePlaneGroupCocycle_radical_hilbertContDiff data basis source cocycle
  have input_regular : ContDiff ℝ ⊤
      (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (point.1, (0 : Fin 2 → ℝ))) :=
    contDiff_fst.prodMk contDiff_const
  have correction := regular.comp input_regular
  convert regular.sub correction using 1
  funext point
  rw [sourcePlaneNormalizedGroupCocycle_hilbert]
  rfl

theorem sourcePlaneNormalizedGroupCocycle_radical_orbital_analyticAt {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (center : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    AnalyticAt ℝ (fun parameter : BinaryRealMatrix × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix parameter.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneNormalizedGroupCocycle data source cocycle
          (SemidirectProduct.inl (Multiplicative.ofAdd parameter.2.1),
            SemidirectProduct.inl (Multiplicative.ofAdd parameter.2.2))).val)) (1, center) := by
  have regular := sourcePlaneGroupCocycle_radical_orbital_analyticAt data basis source cocycle center
  have input_regular : AnalyticAt ℝ
      (fun parameter : BinaryRealMatrix × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
        (parameter.1, (parameter.2.1, (0 : Fin 2 → ℝ)))) (1, center) :=
    analyticAt_fst.prod ((analyticAt_fst.comp analyticAt_snd).prod analyticAt_const)
  have correction := (sourcePlaneGroupCocycle_radical_orbital_analyticAt data basis source cocycle (center.1, 0)).comp
    (f := fun parameter : BinaryRealMatrix × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      (parameter.1, (parameter.2.1, (0 : Fin 2 → ℝ)))) input_regular
  convert regular.sub correction using 1
  funext parameter
  rw [sourcePlaneNormalizedGroupCocycle_hilbert, map_sub]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
