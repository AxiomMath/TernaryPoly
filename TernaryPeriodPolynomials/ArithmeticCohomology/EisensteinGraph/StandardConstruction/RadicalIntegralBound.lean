module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Standard

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RadicalIntegralBound

/-- A summable bound on the rational translates of the fundamental cell gives
both Bochner integrability and a bound on the full integral of the norm. -/
theorem integrable_norm_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : Adeles × Adeles → E) (measurable : AEStronglyMeasurable function radicalMeasure)
    (majorant : (ℚ × ℚ) → ℝ) (nonnegative : ∀ rational, 0 ≤ majorant rational)
    (summable : Summable majorant)
    (bounded : ∀ rational, ∀ coordinates ∈ additiveDomain ×ˢ additiveDomain,
      ‖function (FundamentalDomain.rationalPair rational + coordinates)‖ ≤ majorant rational) :
    Integrable function radicalMeasure ∧
      (∫ coordinates, ‖function coordinates‖ ∂radicalMeasure) ≤ ∑' rational, majorant rational := by
  have estimate : (∫⁻ coordinates, ‖function coordinates‖ₑ ∂radicalMeasure) ≤
      ENNReal.ofReal (∑' rational, majorant rational) := by
    rw [FundamentalDomain.radicalDomain_fundamental.lintegral_eq_tsum''
      (fun coordinates => ‖function coordinates‖ₑ),
      ENNReal.ofReal_tsum_of_nonneg nonnegative summable]
    apply ENNReal.tsum_le_tsum
    intro rational
    calc
      _ ≤ ∫⁻ _coordinates in additiveDomain ×ˢ additiveDomain,
          ENNReal.ofReal (majorant rational) ∂radicalMeasure := by
        apply setLIntegral_mono measurable_const
        intro coordinates membership
        change ‖function (FundamentalDomain.rationalPair rational + coordinates)‖ₑ ≤ _
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (bounded rational coordinates membership)
      _ = ENNReal.ofReal (majorant rational) := by simp
  constructor
  · refine ⟨measurable, ?_⟩
    exact lt_of_le_of_lt estimate (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  · rw [integral_norm_eq_lintegral_enorm measurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top estimate).trans_eq
      (ENNReal.toReal_ofReal (tsum_nonneg nonnegative))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RadicalIntegralBound
