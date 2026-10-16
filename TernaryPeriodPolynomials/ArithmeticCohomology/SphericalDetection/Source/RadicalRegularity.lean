module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.CuspidalAnalyticPullback
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneGroupCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneRadicalMatrix_contDiff {order : WithTop ℕ∞} :
    ContDiff ℝ order (fun coordinates : Fin 2 → ℝ =>
      (realPlaneRadicalMatrix (Multiplicative.ofAdd coordinates)).val) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    first | exact contDiff_const | exact contDiff_apply ℝ ℝ 0 | exact contDiff_apply ℝ ℝ 1

theorem sourcePlaneGroupCocycle_radical_hilbertContDiff {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ContDiff ℝ ⊤ (fun point : (Fin 2 → ℝ) × (Fin 2 → ℝ) => cuspidalTensorHilbertEmbedding data.cusp basis
      (sourcePlaneGroupCocycle data source cocycle
        (SemidirectProduct.inl (Multiplicative.ofAdd point.1), SemidirectProduct.inl (Multiplicative.ofAdd point.2)))) := by
  let points (point : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : Fin 4 → RealGL3 :=
    ![1, realPlaneRadicalMatrix (Multiplicative.ofAdd point.1),
      realPlaneRadicalMatrix (Multiplicative.ofAdd (point.1 + point.2)), 1]
  have input_regular : ContDiff ℝ ⊤ (fun point index => (points point index).val) := by
    apply contDiff_pi.mpr
    intro position
    fin_cases position
    · exact contDiff_const
    · exact realPlaneRadicalMatrix_contDiff.comp contDiff_fst
    · exact realPlaneRadicalMatrix_contDiff.comp (contDiff_fst.add contDiff_snd)
    · exact contDiff_const
  have composed := sourcePlaneCuspidalFamily_hilbertContDiff data basis source cocycle 1 points input_regular
  convert composed using 1
  funext point
  apply congrArg (cuspidalTensorHilbertEmbedding data.cusp basis)
  apply Subtype.ext
  funext argument
  rw [sourcePlaneGroupCocycle_apply]
  change normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
      source ![1, realPlaneMatrix (SemidirectProduct.inl (Multiplicative.ofAdd point.1)),
        realPlaneMatrix (SemidirectProduct.inl (Multiplicative.ofAdd point.1)) *
          realPlaneMatrix (SemidirectProduct.inl (Multiplicative.ofAdd point.2))] (planeLevi argument 1) =
    (sourcePlaneCuspidalValues data source cocycle (fun index => points point index.castSucc)
      (1 * atInfinity (points point (Fin.last 3)))).val argument
  rw [sourcePlaneCuspidalValues_apply, realPlaneMatrix_inl, realPlaneMatrix_inl]
  have tuple : (fun index : Fin 3 => points point index.castSucc) =
      ![1, realPlaneRadicalMatrix (Multiplicative.ofAdd point.1), realPlaneRadicalMatrix (Multiplicative.ofAdd (point.1 + point.2))] := by
    funext position
    fin_cases position <;> rfl
  rw [tuple]
  have product : realPlaneRadicalMatrix (Multiplicative.ofAdd point.1) * realPlaneRadicalMatrix (Multiplicative.ofAdd point.2) =
      realPlaneRadicalMatrix (Multiplicative.ofAdd (point.1 + point.2)) :=
    (realPlaneRadicalMatrix.map_mul _ _).symm
  rw [product]
  change _ = normPower (GeneralLinearGroup.det argument) (-(((degree : ℂ) + 3) / 2)) •
    source _ (planeLevi argument 1 * (1 * atInfinity (1 : RealGL3)))
  rw [atInfinity_one, mul_one, mul_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
