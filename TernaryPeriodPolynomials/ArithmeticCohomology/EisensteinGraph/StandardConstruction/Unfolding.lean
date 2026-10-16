module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FundamentalDomain
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BruhatSums

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Unfolding

open FundamentalDomain

theorem radical_integrable_of_norm_sum (function : Adeles × Adeles → ℂ)
    (translatesIntegrable : ∀ rational : ℚ × ℚ,
      IntegrableOn (fun coordinates => function (rationalPair rational + coordinates))
        (additiveDomain ×ˢ additiveDomain) radicalMeasure)
    (finiteNorm : (∑' rational : ℚ × ℚ,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖function (rationalPair rational + coordinates)‖ₑ ∂radicalMeasure) ≠ ⊤) :
    Integrable function radicalMeasure := by
  have onImages : ∀ rational : ℚ × ℚ, IntegrableOn function
      ((fun coordinates => rationalPair rational + coordinates) ''
        (additiveDomain ×ˢ additiveDomain)) radicalMeasure := by
    intro rational
    exact ((measurePreserving_add_left radicalMeasure (rationalPair rational)).integrableOn_image
      (Homeomorph.addLeft (rationalPair rational)).measurableEmbedding).mpr
        (translatesIntegrable rational)
  have measurable := AEStronglyMeasurable.iUnion
    (fun rational => (onImages rational).aestronglyMeasurable)
  have covers := radicalDomain_fundamental.iUnion_vadd_ae_eq
  change (⋃ rational : ℚ × ℚ,
    (fun coordinates => rationalPair rational + coordinates) ''
      (additiveDomain ×ˢ additiveDomain)) =ᵐ[radicalMeasure] Set.univ at covers
  rw [Measure.restrict_congr_set covers, Measure.restrict_univ] at measurable
  refine ⟨measurable, ?_⟩
  change (∫⁻ coordinates, ‖function coordinates‖ₑ ∂radicalMeasure) < ⊤
  rw [radicalDomain_fundamental.lintegral_eq_tsum'' (fun coordinates => ‖function coordinates‖ₑ)]
  exact lt_top_iff_ne_top.mpr finiteNorm

theorem radical_lintegral_periodization (function : Adeles × Adeles → ℝ≥0∞)
    (measurable : AEMeasurable function radicalMeasure) :
    (∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
      ∑' rational : ℚ × ℚ, function (rationalPair rational + coordinates) ∂radicalMeasure) =
      ∫⁻ coordinates, function coordinates ∂radicalMeasure := by
  rw [lintegral_tsum]
  · exact (radicalDomain_fundamental.lintegral_eq_tsum'' function).symm
  · intro rational
    exact (measurable.comp_quasiMeasurePreserving
      (measurePreserving_add_left radicalMeasure (rationalPair rational)).quasiMeasurePreserving).mono_measure
        Measure.restrict_le_self

theorem radical_integral_periodization (function : Adeles × Adeles → ℂ)
    (integrable : Integrable function radicalMeasure) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      ∑' rational : ℚ × ℚ, function (rationalPair rational + coordinates) ∂radicalMeasure) =
      ∫ coordinates, function coordinates ∂radicalMeasure := by
  rw [integral_tsum]
  · exact (radicalDomain_fundamental.integral_eq_tsum'' function integrable).symm
  · intro rational
    exact (integrable.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_add_left radicalMeasure (rationalPair rational))).mono_measure
        Measure.restrict_le_self
  · change (∑' rational : ℚ × ℚ,
      ∫⁻ coordinates in additiveDomain ×ˢ additiveDomain,
        ‖function (rational +ᵥ coordinates)‖ₑ ∂radicalMeasure) ≠ ⊤
    rw [← radicalDomain_fundamental.lintegral_eq_tsum'' (fun coordinates => ‖function coordinates‖ₑ)]
    exact integrable.hasFiniteIntegral.ne

theorem openCell_integral {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (parameter : ℂ)
    (induced : IsInduced data .plane parameter (extension parameter))
    (argument : AdelicGL)
    (integrable : Integrable (standardIntegrand extension parameter argument) radicalMeasure) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      ∑' rational : ℚ × ℚ, eisensteinSummand extension parameter
        (lineUnipotent coordinates.1 coordinates.2 * argument) (BruhatCells.openFlag rational)
          ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates ∂radicalMeasure := by
  simp_rw [BruhatSums.eisensteinSummand_open_shift data extension parameter induced]
  exact radical_integral_periodization _ integrable

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.Unfolding
