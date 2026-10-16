module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.RationalScaling

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRationalScaling TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicFourierTranslation

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicScaledPoisson

def rationalEquiv (rational : ℚˣ) : (Coordinate → ℚ) ≃ (Coordinate → ℚ) where
  toFun value := rational.val • value
  invFun value := rational.inv • value
  left_inv value := by simp only [smul_smul, rational.inv_val, one_smul]
  right_inv value := by simp only [smul_smul, rational.val_inv, one_smul]

theorem rationalPoint_scale (rational : ℚˣ) (value : Coordinate → ℚ) :
    UnitBoxPoisson.rationalPoint (rationalEquiv rational value) =
      scaleEquiv rational (UnitBoxPoisson.rationalPoint value) := by
  apply Prod.ext
  · ext coordinate
    change ((rational.val * value coordinate : ℚ) : ℝ) = (rational.val : ℝ) * (value coordinate : ℝ)
    exact Rat.cast_mul _ _
  · funext coordinate
    change algebraMap ℚ FiniteAdeles (rational.val * value coordinate) =
      algebraMap ℚ FiniteAdeles rational.val * algebraMap ℚ FiniteAdeles (value coordinate)
    exact map_mul _ _ _

theorem scaleEquiv_inverse (rational : ℚˣ) : scaleEquiv rational⁻¹ = (scaleEquiv rational).symm := by
  apply ContinuousAddEquiv.ext
  intro value
  apply Prod.ext
  · rfl
  · funext coordinate
    rfl

theorem pairing_scale (rational : ℚˣ) (frequency value : Space) :
    pairing frequency (scaleEquiv rational value) = pairing (scaleEquiv rational frequency) value := by
  unfold pairing
  congr 1
  apply Prod.ext
  · change -inner ℝ ((rational.val : ℝ) • value.1) frequency.1 =
      -inner ℝ value.1 ((rational.val : ℝ) • frequency.1)
    rw [real_inner_smul_left, real_inner_smul_right]
  · change -(∑ coordinate, frequency.2 coordinate *
        ((FiniteLatticeMeasure.rationalScale rational).val * value.2 coordinate)) =
      -(∑ coordinate, ((FiniteLatticeMeasure.rationalScale rational).val * frequency.2 coordinate) * value.2 coordinate)
    congr 1
    apply Finset.sum_congr rfl
    intro coordinate _
    ring

theorem pairing_scale_inverse (rational : ℚˣ) (frequency value : Space) :
    pairing (scaleEquiv rational⁻¹ frequency) (scaleEquiv rational value) = pairing frequency value := by
  rw [pairing_scale, scaleEquiv_inverse, ContinuousAddEquiv.apply_symm_apply]

def dilate (function : Space → ℂ) (rational : ℚˣ) (value : Space) : ℂ := function (scaleEquiv rational value)

theorem transform_dilate (function : Space → ℂ) (rational : ℚˣ) (frequency : Space) :
    transform (dilate function rational) frequency = transform function (scaleEquiv rational⁻¹ frequency) := by
  unfold transform dilate
  calc
    (∫ value, pairing frequency value * function (scaleEquiv rational value) ∂measure) =
        ∫ value, pairing (scaleEquiv rational⁻¹ frequency) (scaleEquiv rational value) *
          function (scaleEquiv rational value) ∂measure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun value => by simp only [pairing_scale_inverse])
    _ = _ := integral_scale rational (fun value => pairing (scaleEquiv rational⁻¹ frequency) value * function value)

theorem rational_sum_dilate (function : Space → ℂ) (rational : ℚˣ) :
    (∑' value : Coordinate → ℚ, dilate function rational (UnitBoxPoisson.rationalPoint value)) =
      ∑' value : Coordinate → ℚ, function (UnitBoxPoisson.rationalPoint value) := by
  have equality := (rationalEquiv rational).tsum_eq (fun value => function (UnitBoxPoisson.rationalPoint value))
  simpa only [rationalPoint_scale, dilate] using equality

theorem rational_hasSum_dilate (function : Space → ℂ) (rational : ℚˣ) (sum : ℂ)
    (converges : HasSum (fun value : Coordinate → ℚ => function (UnitBoxPoisson.rationalPoint value)) sum) :
    HasSum (fun value : Coordinate → ℚ => dilate function rational (UnitBoxPoisson.rationalPoint value)) sum := by
  have reindexed := (rationalEquiv rational).hasSum_iff.mpr converges
  change HasSum (fun value => function (UnitBoxPoisson.rationalPoint (rationalEquiv rational value))) sum at reindexed
  simpa only [rationalPoint_scale, dilate] using reindexed

theorem rational_transform_sum_dilate (function : Space → ℂ) (rational : ℚˣ) :
    (∑' value : Coordinate → ℚ, transform (dilate function rational) (UnitBoxPoisson.rationalPoint value)) =
      ∑' value : Coordinate → ℚ, transform function (UnitBoxPoisson.rationalPoint value) := by
  simp only [transform_dilate]
  exact rational_sum_dilate (transform function) rational⁻¹

theorem poisson_dilate_translate (realTest : SchwartzMap RealSpace ℂ) (rational : ℚˣ) (offset : Coordinate → ℚ) :
    (∑' value : Coordinate → ℚ,
      dilate (translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset)) rational
        (UnitBoxPoisson.rationalPoint value)) =
      ∑' value : Coordinate → ℚ,
        transform (dilate (translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset)) rational)
          (UnitBoxPoisson.rationalPoint value) := by
  rw [rational_sum_dilate, rational_transform_sum_dilate]
  exact poisson_translate realTest offset

theorem poisson_dilate_translate_hasSum (realTest : SchwartzMap RealSpace ℂ) (rational : ℚˣ) (offset : Coordinate → ℚ) :
    HasSum (fun value : Coordinate → ℚ =>
      transform (dilate (translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset)) rational)
        (UnitBoxPoisson.rationalPoint value))
      (∑' value : Coordinate → ℚ,
        dilate (translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset)) rational
          (UnitBoxPoisson.rationalPoint value)) := by
  rw [rational_sum_dilate]
  simp only [transform_dilate]
  exact rational_hasSum_dilate _ rational⁻¹ _ (poisson_translate_hasSum realTest offset)

theorem dilate_translate_hasSum (realTest : SchwartzMap RealSpace ℂ) (rational : ℚˣ) (offset : Coordinate → ℚ) :
    HasSum (fun value : Coordinate → ℚ =>
      dilate (translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset)) rational
        (UnitBoxPoisson.rationalPoint value))
      (∑' integer : Coordinate → ℤ, realTest (SchwartzPeriodization.integerVector integer)) :=
  rational_hasSum_dilate _ rational _
    (rational_hasSum_translate _ offset _ (UnitBoxPoisson.rational_hasSum realTest))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicScaledPoisson
