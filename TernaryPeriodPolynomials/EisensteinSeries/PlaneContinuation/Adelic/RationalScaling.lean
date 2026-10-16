module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.FourierTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRationalScaling

instance measure_regular : measure.Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure measure

def realCube : Set RealSpace := (WithLp.toLp 2) '' IntegerCube.cube

theorem realCube_measurable : MeasurableSet realCube :=
  (MeasurableEquiv.toLp 2 (Coordinate → ℝ)).measurableEmbedding.measurableSet_image.mpr IntegerCube.cube_measurable

theorem realCube_measure : (volume : Measure RealSpace) realCube = 1 := by
  rw [← (PiLp.volume_preserving_toLp Coordinate).map_eq]
  have measurable : Measurable (WithLp.toLp 2 : (Coordinate → ℝ) → RealSpace) :=
    (MeasurableEquiv.toLp 2 (Coordinate → ℝ)).measurable
  rw [Measure.map_apply measurable realCube_measurable]
  have preimage : (WithLp.toLp 2) ⁻¹' realCube = IntegerCube.cube :=
    Set.preimage_image_eq _ (WithLp.toLp_injective 2)
  rw [preimage]
  have cube : IntegerCube.cube = Set.univ.pi (fun _ : Coordinate => Set.Ioc (0 : ℝ) 1) := by
    ext value
    simp [IntegerCube.cube]
  rw [cube]
  change Measure.pi (fun _ : Coordinate => (volume : Measure ℝ)) _ = 1
  rw [Measure.pi_pi]
  norm_num

def finiteBox (scale : FiniteAdelesˣ) : Set FiniteRectangularFourier.Space :=
  Set.univ.pi (fun _ => FiniteFourier.lattice scale)

theorem finiteBox_measure (scale : FiniteAdelesˣ) :
    FiniteRectangularFourier.measure (finiteBox scale) =
      (adeleNorm (Norm.finiteAdeleUnit scale) : ℝ≥0∞) ^ 6 := by
  rw [FiniteRectangularFourier.measure, finiteBox, Measure.pi_pi]
  simp only [FiniteLatticeMeasure.lattice_measure, Finset.prod_const, Finset.card_univ]
  rfl

theorem finiteBox_image (scale : FiniteAdelesˣ) :
    (fun value : FiniteRectangularFourier.Space => fun coordinate => scale.val * value coordinate) '' finiteBox 1 =
      finiteBox scale := by
  ext value
  constructor
  · rintro ⟨preimage, membership, rfl⟩ coordinate _
    obtain ⟨integral, equality⟩ := membership coordinate (Set.mem_univ _)
    refine ⟨integral, ?_⟩
    change scale.val * integralEmbedding integral = scale.val * preimage coordinate
    simpa only [Units.val_one, one_mul] using congrArg (fun value => scale.val * value) equality
  · intro membership
    have coordinates : ∀ coordinate, ∃ integral : IntegralAdeles,
        scale.val * integralEmbedding integral = value coordinate :=
      fun coordinate => membership coordinate (Set.mem_univ _)
    choose integrals equality using coordinates
    refine ⟨fun coordinate => integralEmbedding (integrals coordinate), ?_, funext equality⟩
    intro coordinate _
    exact ⟨integrals coordinate, by simp⟩

def scaleEquiv (rational : ℚˣ) : Space ≃ₜ+ Space where
  toFun value := ((rational.val : ℝ) • value.1,
    fun coordinate => (FiniteLatticeMeasure.rationalScale rational).val * value.2 coordinate)
  invFun value := (((rational⁻¹).val : ℝ) • value.1,
    fun coordinate => (FiniteLatticeMeasure.rationalScale rational).inv * value.2 coordinate)
  left_inv value := by
    apply Prod.ext
    · change ((rational⁻¹).val : ℝ) • ((rational.val : ℝ) • value.1) = value.1
      rw [smul_smul, ← Rat.cast_mul]
      change ((rational.inv * rational.val : ℚ) : ℝ) • value.1 = value.1
      rw [rational.inv_val, Rat.cast_one, one_smul]
    · funext coordinate
      change (FiniteLatticeMeasure.rationalScale rational).inv *
        ((FiniteLatticeMeasure.rationalScale rational).val * value.2 coordinate) = value.2 coordinate
      rw [← mul_assoc, (FiniteLatticeMeasure.rationalScale rational).inv_val, one_mul]
  right_inv value := by
    apply Prod.ext
    · change (rational.val : ℝ) • (((rational⁻¹).val : ℝ) • value.1) = value.1
      rw [smul_smul, ← Rat.cast_mul]
      change ((rational.val * rational.inv : ℚ) : ℝ) • value.1 = value.1
      rw [rational.val_inv, Rat.cast_one, one_smul]
    · funext coordinate
      change (FiniteLatticeMeasure.rationalScale rational).val *
        ((FiniteLatticeMeasure.rationalScale rational).inv * value.2 coordinate) = value.2 coordinate
      rw [← mul_assoc, (FiniteLatticeMeasure.rationalScale rational).val_inv, one_mul]
  map_add' first second := by
    apply Prod.ext
    · exact smul_add _ _ _
    · funext coordinate
      exact mul_add _ _ _
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_const_smul (rational.val : ℝ)).comp (continuous_fst : Continuous (fun value : Space => value.1))
    · apply continuous_pi
      intro coordinate
      exact (continuous_const.mul ((continuous_apply coordinate).comp
        (continuous_snd : Continuous (fun value : Space => value.2))) :
        Continuous (fun value : Space => (FiniteLatticeMeasure.rationalScale rational).val * value.2 coordinate))
  continuous_invFun := by
    apply Continuous.prodMk
    · exact (continuous_const_smul ((rational⁻¹).val : ℝ)).comp (continuous_fst : Continuous (fun value : Space => value.1))
    · apply continuous_pi
      intro coordinate
      exact (continuous_const.mul ((continuous_apply coordinate).comp
        (continuous_snd : Continuous (fun value : Space => value.2))) :
        Continuous (fun value : Space => (FiniteLatticeMeasure.rationalScale rational).inv * value.2 coordinate))

def baseDomain : Set Space := realCube ×ˢ finiteBox 1

theorem baseDomain_measure : measure baseDomain = 1 := by
  rw [AdelicRectangularFourier.measure, baseDomain, Measure.prod_prod, realCube_measure, finiteBox_measure,
    FiniteLatticeMeasure.finiteUnit_one, map_one]
  norm_num

theorem baseDomain_image (rational : ℚˣ) :
    scaleEquiv rational '' baseDomain = ((rational.val : ℝ) • realCube) ×ˢ
      finiteBox (FiniteLatticeMeasure.rationalScale rational) := by
  change (fun value : Space => ((rational.val : ℝ) • value.1,
      fun coordinate => (FiniteLatticeMeasure.rationalScale rational).val * value.2 coordinate)) ''
    (realCube ×ˢ finiteBox 1) = _
  rw [← Set.prod_image_image_eq
    (m₁ := fun value : RealSpace => (rational.val : ℝ) • value)
    (m₂ := fun value : FiniteRectangularFourier.Space =>
      fun coordinate => (FiniteLatticeMeasure.rationalScale rational).val * value coordinate), finiteBox_image]
  rfl

theorem baseDomain_image_measure (rational : ℚˣ) : measure (scaleEquiv rational '' baseDomain) = 1 := by
  rw [baseDomain_image, AdelicRectangularFourier.measure, Measure.prod_prod, Measure.addHaar_smul, realCube_measure, mul_one, finiteBox_measure]
  have dimension : Module.finrank ℝ RealSpace = 6 := by simp [RealSpace, Coordinate]
  rw [dimension]
  have finiteNorm : (adeleNorm (Norm.finiteAdeleUnit (FiniteLatticeMeasure.rationalScale rational)) : ℝ) =
      |(rational.val : ℝ)|⁻¹ :=
    (FiniteLatticeMeasure.lattice_real_measure _).symm.trans (FiniteLatticeMeasure.rational_lattice_measure rational)
  have finiteNormENN : (adeleNorm (Norm.finiteAdeleUnit (FiniteLatticeMeasure.rationalScale rational)) : ℝ≥0∞) =
      ENNReal.ofReal (|(rational.val : ℝ)|⁻¹) := by
    rw [← ENNReal.ofReal_coe_nnreal, finiteNorm]
  rw [finiteNormENN, abs_pow, ← ENNReal.ofReal_pow (inv_nonneg.mpr (abs_nonneg _)),
    ← ENNReal.ofReal_mul (pow_nonneg (abs_nonneg _) _)]
  have realNonzero : (rational.val : ℝ) ≠ 0 := by exact_mod_cast rational.ne_zero
  rw [← mul_pow, mul_inv_cancel₀ (abs_ne_zero.mpr realNonzero), one_pow, ENNReal.ofReal_one]

theorem scale_haarChar (rational : ℚˣ) : addEquivAddHaarChar (scaleEquiv rational) = 1 := by
  have equality := addEquivAddHaarChar_smul_preimage measure (scaleEquiv rational)
    (X := scaleEquiv rational '' baseDomain)
  rw [Set.preimage_image_eq _ (scaleEquiv rational).injective,
    baseDomain_measure, baseDomain_image_measure] at equality
  change (addEquivAddHaarChar (scaleEquiv rational) : ℝ≥0∞) * 1 = 1 at equality
  exact ENNReal.coe_injective (by simpa only [mul_one, ENNReal.coe_one] using equality)

theorem scale_measurePreserving (rational : ℚˣ) : MeasurePreserving (scaleEquiv rational) measure measure := by
  refine ⟨(scaleEquiv rational).continuous.measurable, ?_⟩
  have equality := addEquivAddHaarChar_smul_map measure (scaleEquiv rational)
  simpa only [scale_haarChar, one_smul] using equality

theorem integral_scale (rational : ℚˣ) (function : Space → ℂ) :
    ∫ value, function (scaleEquiv rational value) ∂measure = ∫ value, function value ∂measure :=
  (scale_measurePreserving rational).integral_comp
    (scaleEquiv rational).toHomeomorph.toMeasurableEquiv.measurableEmbedding function

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRationalScaling
