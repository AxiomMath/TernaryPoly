module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceMeasureSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic TopologicalSpace MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

instance finitePadicMeasurableSpace (prime : ℕ) [Fact prime.Prime] : MeasurableSpace ℚ_[prime] :=
  borel ℚ_[prime]

instance finitePadicBorelSpace (prime : ℕ) [Fact prime.Prime] : BorelSpace ℚ_[prime] := ⟨rfl⟩

theorem finiteCompletionPadic_integral_iff (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ value : place.adicCompletion ℚ,
      ‖finiteCompletionPadicEquiv place value‖ ≤ 1 ↔ value ∈ place.adicCompletionIntegers ℚ := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro value
  constructor
  · intro integral
    let integer : ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val] :=
      ⟨finiteCompletionPadicEquiv place value, integral⟩
    have equality := finitePadicEquiv_inverse_compatible place integer
    rw [RingEquiv.symm_apply_apply] at equality
    exact equality ▸ ((finiteIntegralPadicEquiv place).symm integer).property
  · intro integral
    have equality := finitePadicEquiv_compatible place ⟨value, integral⟩
    rw [← equality]
    exact (finiteIntegralPadicEquiv place ⟨value, integral⟩).property

def finitePadicMeasure (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] :=
  Measure.map (finiteCompletionPadicAddEquiv place) (finiteCompletionMeasure place)

instance finitePadicMeasure_haar (place : FinitePlace) : (finitePadicMeasure place).IsAddHaarMeasure :=
  (finiteCompletionPadicAddEquiv place).isAddHaarMeasure_map (finiteCompletionMeasure place)

instance finitePadicMeasure_sigmaFinite (place : FinitePlace) : SigmaFinite (finitePadicMeasure place) :=
  inferInstance

theorem finitePadicMeasure_normalized (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    finitePadicMeasure place {value | ‖value‖ ≤ 1} = 1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have measurable : Measurable (finiteCompletionPadicAddEquiv place :
      place.adicCompletion ℚ → ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) :=
    (finiteCompletionPadicAddEquiv place).continuous.measurable
  change Measure.map (finiteCompletionPadicAddEquiv place) (finiteCompletionMeasure place) _ = 1
  rw [Measure.map_apply measurable (isClosed_le continuous_norm continuous_const).measurableSet]
  have preimage : (finiteCompletionPadicAddEquiv place) ⁻¹' {value | ‖value‖ ≤ 1} =
      (place.adicCompletionIntegers ℚ : Set (place.adicCompletion ℚ)) := by
    ext value
    exact finiteCompletionPadic_integral_iff place value
  rw [preimage, finiteCompletionMeasure_normalized]

theorem finiteCompletionPadic_measurePreserving (place : FinitePlace) :
    MeasurePreserving (finiteCompletionPadicAddEquiv place) (finiteCompletionMeasure place) (finitePadicMeasure place) :=
  ⟨(finiteCompletionPadicAddEquiv place).continuous.measurable, rfl⟩

theorem finiteCompletionPadic_symm_measurePreserving (place : FinitePlace) :
    MeasurePreserving (finiteCompletionPadicAddEquiv place).symm (finitePadicMeasure place) (finiteCompletionMeasure place) :=
  MeasurePreserving.symm (finiteCompletionPadicAddEquiv place).toHomeomorph.toMeasurableEquiv
    (finiteCompletionPadic_measurePreserving place)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
