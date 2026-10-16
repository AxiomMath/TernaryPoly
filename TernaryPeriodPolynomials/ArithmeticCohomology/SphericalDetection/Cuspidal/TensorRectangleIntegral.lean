module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorCalculus
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.AnalyticRadicalAction
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

theorem cuspidalTensorPartialIntegral_orbital_analyticAt
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (values : ℝ × ℝ → cuspidalTensorValues cusp V)
    (continuous : Continuous (fun real => cuspidalTensorHilbertEmbedding cusp basis (values real)))
    (analytic : ∀ center : ℝ × ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × (ℝ × ℝ) =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center))
    (left right center : ℝ) :
    AnalyticAt ℝ (fun point : BinaryRealMatrix × ℝ =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (∫ sample in left..right, cuspidalTensorHilbertEmbedding cusp basis
          (values (point.2, sample)))) (1, center) := by
  let function (point : (BinaryRealMatrix × ℝ) × ℝ) :=
    binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1.1))
      (cuspidalTensorHilbertEmbedding cusp basis (values (point.1.2, point.2)))
  have reindexed (sample : ℝ) : AnalyticAt ℝ function ((1, center), sample) := by
    have input : AnalyticAt ℝ
        (fun point : (BinaryRealMatrix × ℝ) × ℝ => (point.1.1, (point.1.2, point.2)))
        ((1, center), sample) :=
      (analyticAt_fst.comp analyticAt_fst).prod
        ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)
    exact (analytic (center, sample)).comp
      (f := fun point : (BinaryRealMatrix × ℝ) × ℝ => (point.1.1, (point.1.2, point.2)))
      (x := ((1, center), sample)) input
  have integrated := analyticAt_intervalIntegral function (1, center) Set.univ isOpen_univ
    (Set.mem_univ _) (by
      intro point _
      exact (binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))).continuous.comp
        (continuous.comp (show Continuous (fun sample : ℝ => (point.2, sample)) from
          continuous_const.prodMk continuous_id))) reindexed left right
  apply integrated.congr
  filter_upwards [] with point
  dsimp only [function]
  have integrable : IntervalIntegrable
      (fun sample => cuspidalTensorHilbertEmbedding cusp basis (values (point.2, sample)))
      volume left right :=
    (continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable left right
  exact (binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))).intervalIntegral_comp_comm
    integrable

theorem cuspidalTensorRectangleIntegral_exists
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ V)
    (values : ℝ × ℝ → cuspidalTensorValues cusp V)
    (continuous : Continuous (fun real => cuspidalTensorHilbertEmbedding cusp basis (values real)))
    (fixed : ∀ real, values real ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : ∀ center : ℝ × ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × (ℝ × ℝ) =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (values point.2))) (1, center))
    (left₁ right₁ left₂ right₂ : ℝ) (ordered₁ : left₁ ≤ right₁) (ordered₂ : left₂ ≤ right₂) :
    ∃ result : cuspidalTensorValues cusp V,
      cuspidalTensorHilbertEmbedding cusp basis result =
        ∫ real in Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂,
          cuspidalTensorHilbertEmbedding cusp basis (values real)
            ∂((volume : Measure ℝ).prod volume) ∧
      result ∈ cuspidalTensorFiniteLevel cusp V := by
  have section_analytic (first center : ℝ) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (values (first, point.2)))) (1, center) := by
    have input : AnalyticAt ℝ
        (fun point : BinaryRealMatrix × ℝ => (point.1, (first, point.2))) (1, center) :=
      analyticAt_fst.prod (analyticAt_const.prod analyticAt_snd)
    exact (analytic (first, center)).comp
      (f := fun point : BinaryRealMatrix × ℝ => (point.1, (first, point.2)))
      (x := (1, center)) input
  have sections (first : ℝ) := cuspidalTensorIntervalIntegral_exists cusp basis
    (fun second => values (first, second))
    (continuous.comp (continuous_const.prodMk continuous_id))
    (fun second => fixed (first, second)) (section_analytic first) left₂ right₂
  choose slices partial_eq partial_fixed using sections
  have partial_analytic (center : ℝ) : AnalyticAt ℝ
      (fun point : BinaryRealMatrix × ℝ =>
        binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding cusp basis (slices point.2))) (1, center) := by
    simpa only [partial_eq] using cuspidalTensorPartialIntegral_orbital_analyticAt
      cusp basis values continuous analytic left₂ right₂ center
  have partial_continuous :
      Continuous (fun first => cuspidalTensorHilbertEmbedding cusp basis (slices first)) :=
    (cuspidalTensorFamily_contDiff_of_orbital cusp basis slices partial_analytic).continuous
  obtain ⟨result, result_eq, result_fixed⟩ := cuspidalTensorIntervalIntegral_exists cusp basis
    slices partial_continuous partial_fixed partial_analytic left₁ right₁
  refine ⟨result, ?_, result_fixed⟩
  rw [result_eq]
  simp only [partial_eq]
  have integrable : IntegrableOn (fun real => cuspidalTensorHilbertEmbedding cusp basis (values real))
      (Set.Icc left₁ right₁ ×ˢ Set.Icc left₂ right₂) ((volume : Measure ℝ).prod volume) :=
    continuous.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [setIntegral_prod _ integrable, intervalIntegral.integral_of_le ordered₁]
  rw [← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro first _
  dsimp only
  rw [intervalIntegral.integral_of_le ordered₂, integral_Icc_eq_integral_Ioc]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
