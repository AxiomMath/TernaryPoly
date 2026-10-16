module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RadicalRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalOrbitalAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem sourcePlaneGroupCocycle_radical_values {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) (first second : Fin 2 → ℝ) :
    sourcePlaneGroupCocycle data source cocycle
      (SemidirectProduct.inl (Multiplicative.ofAdd first), SemidirectProduct.inl (Multiplicative.ofAdd second)) =
    sourcePlaneCuspidalValues data source cocycle
      ![1, realPlaneRadicalMatrix (Multiplicative.ofAdd first), realPlaneRadicalMatrix (Multiplicative.ofAdd (first + second))] 1 := by
  apply Subtype.ext
  funext argument
  rw [sourcePlaneGroupCocycle_apply, sourcePlaneCuspidalValues_apply, realPlaneMatrix_inl, realPlaneMatrix_inl, mul_one]
  have product : realPlaneRadicalMatrix (Multiplicative.ofAdd first) * realPlaneRadicalMatrix (Multiplicative.ofAdd second) =
      realPlaneRadicalMatrix (Multiplicative.ofAdd (first + second)) :=
    (realPlaneRadicalMatrix.map_mul _ _).symm
  rw [product]

theorem sourcePlaneGroupCocycle_radical_orbital_analyticAt {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (center : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    AnalyticAt ℝ (fun parameter : BinaryRealMatrix × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix parameter.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis (sourcePlaneGroupCocycle data source cocycle
          (SemidirectProduct.inl (Multiplicative.ofAdd parameter.2.1), SemidirectProduct.inl (Multiplicative.ofAdd parameter.2.2)))))
      (1, center) := by
  let vertices (point : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Fin 3 → RealGL3 :=
    ![1, realPlaneRadicalMatrix (Multiplicative.ofAdd point.1), realPlaneRadicalMatrix (Multiplicative.ofAdd (point.1 + point.2))]
  have input_regular : ContDiff ℝ ⊤ (fun point index => (vertices point index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_const
    · exact realPlaneRadicalMatrix_contDiff.comp contDiff_fst
    · exact realPlaneRadicalMatrix_contDiff.comp (contDiff_fst.add contDiff_snd)
  have analytic := sourcePlaneCuspidalValues_orbital_analyticAt data basis source cocycle vertices center input_regular.contDiffAt
  convert analytic using 1
  funext parameter
  rw [sourcePlaneGroupCocycle_radical_values]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
