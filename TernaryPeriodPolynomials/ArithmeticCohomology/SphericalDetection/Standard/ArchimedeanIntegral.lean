module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.GoodLineFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def awayRadicalJoin : ((ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) ≃ₜ
    (AdelesAwayThree × AdelesAwayThree) :=
  Homeomorph.prodProdProdComm ℝ ℝ FiniteAwayThree FiniteAwayThree

theorem awayRadicalJoin_measurePreserving :
    MeasurePreserving awayRadicalJoin
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))
      radicalAwayThreeMeasure :=
  measurePreserving_prodTranspose volume volume finiteAwayThreeMeasure finiteAwayThreeMeasure

def standardGoodLineRealArgument (real : ℝ × ℝ) : RealGL3 :=
  weyl⁻¹ * lineUnipotent real.1 real.2 *
    GeneralLinearGroup.map (algebraMap ℚ ℝ) rationalGoodLine

def standardGoodLineFiniteArgument (finite : FiniteAwayThree × FiniteAwayThree) : FiniteGL :=
  weyl⁻¹ * lineUnipotent finite.1.val finite.2.val * rationalFinite rationalGoodLine

theorem standardGoodLineArgument_combine (real : ℝ × ℝ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    weyl⁻¹ * lineUnipotent (adeleAwayThreeScalar (real.1, finite.1))
      (adeleAwayThreeScalar (real.2, finite.2)) * rationalGroup rationalGoodLine =
    combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite) := by
  apply adelicGL_ext
  · rw [realGroup_combineGL, map_mul, map_mul, map_inv, realGroup_rational]
    change (GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) weyl)⁻¹ *
      GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)
        (lineUnipotent (adeleAwayThreeScalar (real.1, finite.1))
          (adeleAwayThreeScalar (real.2, finite.2))) * _ = _
    rw [map_weyl, map_lineUnipotent]
    rfl
  · rw [finiteGroup_combineGL, map_mul, map_mul, map_inv, finiteGroup_rational]
    change (GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) weyl)⁻¹ *
      GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)
        (lineUnipotent (adeleAwayThreeScalar (real.1, finite.1))
          (adeleAwayThreeScalar (real.2, finite.2))) * _ = _
    rw [map_weyl, map_lineUnipotent]
    rfl

/-- The remaining real integral retains the exact finite argument and matrix convention. -/
def standardGoodLineArchimedeanIntegral (flat : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  ∫ real : ℝ × ℝ, flat parameter
    (combineGL (standardGoodLineRealArgument real) (standardGoodLineFiniteArgument finite))
    ∂((volume : Measure ℝ).prod volume)

theorem standardGoodLineAwayIntegral_fubini (flat : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (integrable : Integrable (standardGoodLineAwayIntegrand flat parameter) radicalAwayThreeMeasure) :
    Integrable (standardGoodLineArchimedeanIntegral flat parameter)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
    (∫ away, standardGoodLineAwayIntegrand flat parameter away ∂radicalAwayThreeMeasure) =
      ∫ finite, standardGoodLineArchimedeanIntegral flat parameter finite
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have lifted := awayRadicalJoin_measurePreserving.integrable_comp_of_integrable integrable
  have inner : (fun finite => ∫ real : ℝ × ℝ,
      standardGoodLineAwayIntegrand flat parameter (awayRadicalJoin (real, finite))
        ∂((volume : Measure ℝ).prod volume)) =
      standardGoodLineArchimedeanIntegral flat parameter := by
    funext finite
    apply integral_congr_ae
    filter_upwards [] with real
    change flat parameter (weyl⁻¹ * lineUnipotent (adeleAwayThreeScalar (real.1, finite.1))
      (adeleAwayThreeScalar (real.2, finite.2)) * rationalGroup rationalGoodLine) = _
    rw [standardGoodLineArgument_combine]
  constructor
  · rw [← inner]
    exact lifted.integral_prod_right
  · rw [← awayRadicalJoin_measurePreserving.integral_comp awayRadicalJoin.measurableEmbedding]
    have split := integral_prod_symm _ lifted
    dsimp only [Function.comp_def] at split
    rw [split, inner]

theorem standardContinuation_goodLine_archimedean_finite {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → AdelicGL → ℂ)
    (flat_section : IsFlatSection data flat)
    (endpoint_support : LocalThreePlaneSupport (flat cohomologicalPoint))
    (continuation : IsStandardContinuation flat standard) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (standardGoodLineArchimedeanIntegral flat parameter)
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) ∧
      standard parameter (rationalGroup rationalGoodLine) =
        (1 / 9 : ℂ) * ∫ finite, standardGoodLineArchimedeanIntegral flat parameter finite
          ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  obtain ⟨threshold, formula⟩ :=
    standardContinuation_goodLine_factor local_entry data flat standard flat_section endpoint_support continuation
  refine ⟨threshold, ?_⟩
  intro parameter beyond
  obtain ⟨integrable, value⟩ := formula parameter beyond
  obtain ⟨integrated, split⟩ := standardGoodLineAwayIntegral_fubini flat parameter integrable
  exact ⟨integrated, value.trans (congrArg ((1 / 9 : ℂ) * ·) split)⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
