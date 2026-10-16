module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.AdelicIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Truncation

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertCellRealization

theorem cellIntegral_has_realization {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) (rational : ℚ × ℚ) :
    ∃ vector : data.cusp.smooth,
      vector.val = HilbertTruncation.cellIntegral data extension flat parameter argument rational ∧
      ∀ test, data.cusp.realize vector test =
        ∫ coordinates in additiveDomain ×ˢ additiveDomain,
          data.cusp.realize (CuspLift.vector data .plane parameter (extension parameter)
            (flat.1 parameter) (weyl⁻¹ *
              lineUnipotent (FundamentalDomain.rationalPair rational + coordinates).1
                (FundamentalDomain.rationalPair rational + coordinates).2 * argument)) test
            ∂radicalMeasure := by
  let argumentMap : Adeles × Adeles → AdelicGL := fun coordinates => weyl⁻¹ *
    lineUnipotent (FundamentalDomain.rationalPair rational + coordinates).1
      (FundamentalDomain.rationalPair rational + coordinates).2 * argument
  have argumentContinuous : Continuous argumentMap :=
    (continuous_const.mul (InducedContinuity.lineUnipotent_continuous.comp
      (continuous_const.add continuous_id))).mul continuous_const
  exact CompactAdelicIntegral.compact_set_integral data parameter (extension parameter)
    (flat.1 parameter) radicalMeasure
    (InducedContinuity.additiveCompact ×ˢ InducedContinuity.additiveCompact)
    (additiveDomain ×ˢ additiveDomain)
    (InducedContinuity.additiveCompact_isCompact.prod
      InducedContinuity.additiveCompact_isCompact)
    (Set.prod_mono InducedContinuity.additiveDomain_subset_compact
      InducedContinuity.additiveDomain_subset_compact) argumentMap argumentContinuous

theorem cellIntegral_mem_smooth {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) (rational : ℚ × ℚ) :
    HilbertTruncation.cellIntegral data extension flat parameter argument rational ∈
      data.cusp.smooth := by
  obtain ⟨vector, equality, _⟩ :=
    cellIntegral_has_realization data extension flat parameter argument rational
  exact equality ▸ vector.property

def cellVector {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) (rational : ℚ × ℚ) : data.cusp.smooth :=
  ⟨HilbertTruncation.cellIntegral data extension flat parameter argument rational,
    cellIntegral_mem_smooth data extension flat parameter argument rational⟩

theorem cellVector_realizes {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) (rational : ℚ × ℚ) (test : BinaryAdelicGL) :
    data.cusp.realize (cellVector data extension flat parameter argument rational) test =
      ∫ coordinates in additiveDomain ×ˢ additiveDomain,
        data.cusp.realize (CuspLift.vector data .plane parameter (extension parameter)
          (flat.1 parameter) (weyl⁻¹ *
            lineUnipotent (FundamentalDomain.rationalPair rational + coordinates).1
              (FundamentalDomain.rationalPair rational + coordinates).2 * argument)) test
          ∂radicalMeasure := by
  obtain ⟨vector, equality, scalar⟩ :=
    cellIntegral_has_realization data extension flat parameter argument rational
  have same : cellVector data extension flat parameter argument rational = vector :=
    Subtype.ext equality.symm
  exact same ▸ scalar test

theorem cellVector_realizes_one {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (argument : AdelicGL) (rational : ℚ × ℚ) :
    data.cusp.realize (cellVector data extension flat parameter argument rational) 1 =
      ∫ coordinates in additiveDomain ×ˢ additiveDomain,
        standardIntegrand extension parameter argument
          (FundamentalDomain.rationalPair rational + coordinates) ∂radicalMeasure := by
  rw [cellVector_realizes]
  apply integral_congr_ae
  filter_upwards [] with coordinates
  simp only [CuspLift.realizes, map_one, ParabolicInvariance.normPower_one,
    binaryLevi, ParabolicInvariance.planeLevi_one, one_mul]
  rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertCellRealization
