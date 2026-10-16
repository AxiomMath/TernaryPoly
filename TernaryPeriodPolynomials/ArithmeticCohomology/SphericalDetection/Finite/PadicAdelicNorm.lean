module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceUnitSplitting
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.HaarNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteMeasure_padicUnit_preimage (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ unit : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]ˣ,
      finiteMeasure ((fun value => (finiteAtPadicUnit place unit).val * value) ⁻¹' Set.range integralEmbedding) =
        (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞)⁻¹ := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro unit
  have transported := (finitePadicSplit_symm_measurePreserving place).measure_preimage_emb
    (finitePadicSplit place).symm.toHomeomorph.measurableEmbedding
    ((fun value => (finiteAtPadicUnit place unit).val * value) ⁻¹' Set.range integralEmbedding)
  have preimage : (finitePadicSplit place).symm ⁻¹'
      ((fun value => (finiteAtPadicUnit place unit).val * value) ⁻¹' Set.range integralEmbedding) =
      {value | ‖unit.val * value‖ ≤ 1} ×ˢ (Subtype.val ⁻¹' Set.range integralEmbedding) := by
    ext pair
    change (finiteAtPadicUnit place unit).val * (finitePadicSplit place).symm pair ∈
      Set.range integralEmbedding ↔ _
    rw [finiteAtPadicUnit_mul_split, finitePadicSplit_integral_iff]
    rfl
  rw [← transported, preimage, Measure.prod_prod, finiteAwayPlaceMeasure_normalized, mul_one]
  exact padicHaarChar_ball_measure (finitePadicMeasure place) (finitePadicMeasure_normalized place) unit

theorem adeleNorm_finiteAtPadicUnit (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ unit : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]ˣ,
      (adeleNorm (finiteAdeleUnit (finiteAtPadicUnit place unit)) : ℝ) = ‖unit.val‖ := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro unit
  let box : Set Adeles := Set.Icc (0 : ℝ) 1 ×ˢ Set.range integralEmbedding
  have preimage : (ContinuousAddEquiv.mulLeft (finiteAdeleUnit (finiteAtPadicUnit place unit))) ⁻¹' box =
      Set.Icc (0 : ℝ) 1 ×ˢ
        ((fun value => (finiteAtPadicUnit place unit).val * value) ⁻¹' Set.range integralEmbedding) := by
    ext point
    change (0 ≤ 1 * point.1 ∧ 1 * point.1 ≤ 1) ∧ _ ↔ (0 ≤ point.1 ∧ point.1 ≤ 1) ∧ _
    rw [one_mul]
    rfl
  have volume : adeleMeasure box = 1 := by
    rw [adeleMeasure, Measure.prod_prod, finiteMeasure_integralLattice]
    norm_num
  have preimage_volume : adeleMeasure
      ((ContinuousAddEquiv.mulLeft (finiteAdeleUnit (finiteAtPadicUnit place unit))) ⁻¹' box) =
      (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞)⁻¹ := by
    rw [preimage, adeleMeasure, Measure.prod_prod, finiteMeasure_padicUnit_preimage]
    norm_num
  have scaling := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := box) (ContinuousAddEquiv.mulLeft (finiteAdeleUnit (finiteAtPadicUnit place unit)))
  rw [volume, preimage_volume] at scaling
  change (adeleNorm (finiteAdeleUnit (finiteAtPadicUnit place unit)) : ℝ≥0∞) *
    (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft unit) : ℝ≥0∞)⁻¹ = 1 at scaling
  have equality := ENNReal.eq_inv_of_mul_eq_one_left scaling
  rw [inv_inv] at equality
  have real_equality := congrArg ENNReal.toReal equality
  simp only [ENNReal.coe_toReal] at real_equality
  exact real_equality.trans (padicHaarChar_eq_norm (finitePadicMeasure place) (finitePadicMeasure_normalized place) unit)

theorem normPower_finiteAtPadicUnit (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (unit : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]ˣ) (exponent : ℂ),
      normPower (finiteAdeleUnit (finiteAtPadicUnit place unit)) exponent =
        Complex.exp (exponent * (Real.log ‖unit.val‖ : ℂ)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro unit exponent
  rw [normPower, adeleNorm_finiteAtPadicUnit]

theorem normPower_det_finiteAtPadicGL (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (matrix : GeneralLinearGroup (Fin 2) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) (exponent : ℂ),
      normPower (GeneralLinearGroup.det (atFinite (finiteAtPadicGL 2 place matrix))) exponent =
        Complex.exp (exponent * (Real.log ‖(GeneralLinearGroup.det matrix).val‖ : ℂ)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro matrix exponent
  rw [binary_det_atFinite, finiteAtPadicGL_det, normPower_finiteAtPadicUnit]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
