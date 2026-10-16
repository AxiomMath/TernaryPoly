module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearDomain

@[expose] public section


open Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def integerSpecialLinearQuotientMeasure :
    Measure (Quotient (MulAction.orbitRel integerSpecialLinearSubgroup (SpecialLinearGroup (Fin 3) ℝ))) :=
  Measure.map (Quotient.mk (MulAction.orbitRel integerSpecialLinearSubgroup (SpecialLinearGroup (Fin 3) ℝ)))
    (realSpecialLinearHaar.restrict integerSpecialLinearDomain)

theorem integerSpecialLinearQuotientMeasure_eq_map
    {domain : Set (SpecialLinearGroup (Fin 3) ℝ)}
    (fundamental : IsFundamentalDomain integerSpecialLinearSubgroup domain realSpecialLinearHaar) :
    integerSpecialLinearQuotientMeasure =
      Measure.map (Quotient.mk (MulAction.orbitRel integerSpecialLinearSubgroup (SpecialLinearGroup (Fin 3) ℝ)))
        (realSpecialLinearHaar.restrict domain) :=
  integerSpecialLinearDomain_fundamental.quotientMeasure_eq realSpecialLinearHaar fundamental

instance integerSpecialLinearQuotientMeasure_compatible :
    QuotientMeasureEqMeasurePreimage realSpecialLinearHaar integerSpecialLinearQuotientMeasure :=
  ⟨fun _ fundamental => integerSpecialLinearQuotientMeasure_eq_map fundamental⟩

instance integerSpecialLinearQuotientMeasure_sigmaFinite : SigmaFinite integerSpecialLinearQuotientMeasure :=
  QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient
    (ν := realSpecialLinearHaar) integerSpecialLinearQuotientMeasure

theorem integerSpecialLinearQuotientMeasure_univ :
    integerSpecialLinearQuotientMeasure Set.univ = realSpecialLinearHaar integerSpecialLinearDomain := by
  rw [integerSpecialLinearQuotientMeasure, Measure.map_apply_of_aemeasurable]
  · simp only [Set.preimage_univ, Measure.restrict_apply_univ]
  · exact measurable_quotient_mk''.aemeasurable
  · exact MeasurableSet.univ

theorem integerSpecialLinearQuotientMeasure_univ_ne_zero :
    integerSpecialLinearQuotientMeasure Set.univ ≠ 0 := by
  rw [integerSpecialLinearQuotientMeasure_univ]
  exact integerSpecialLinearDomain_fundamental.measure_ne_zero (NeZero.ne realSpecialLinearHaar)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
