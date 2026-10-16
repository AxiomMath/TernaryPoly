module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnitBoxPoisson

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicFourierTranslation

instance measure_isAddHaar : measure.IsAddHaarMeasure :=
  inferInstanceAs (((volume : Measure RealSpace).prod
    (Measure.pi (fun _ : Coordinate => finiteMeasure))).IsAddHaarMeasure)

theorem rationalPoint_add (first second : Coordinate → ℚ) :
    UnitBoxPoisson.rationalPoint (first + second) =
      UnitBoxPoisson.rationalPoint first + UnitBoxPoisson.rationalPoint second := by
  apply Prod.ext
  · ext coordinate
    exact Rat.cast_add _ _
  · funext coordinate
    exact map_add (algebraMap ℚ FiniteAdeles) _ _

theorem rationalPoint_neg (value : Coordinate → ℚ) :
    UnitBoxPoisson.rationalPoint (-value) = -UnitBoxPoisson.rationalPoint value := by
  apply Prod.ext
  · ext coordinate
    exact Rat.cast_neg _
  · funext coordinate
    exact map_neg (algebraMap ℚ FiniteAdeles) _

theorem pairing_zero (frequency : Space) : pairing frequency 0 = 1 := by
  rw [pairing]
  have equality : (-inner ℝ (0 : RealSpace) frequency.1,
      -(∑ coordinate, frequency.2 coordinate * (0 : FiniteRectangularFourier.Space) coordinate)) = (0 : Adeles) := by simp
  exact equality ▸ AdelicCharacter.phase_zero

theorem pairing_add (frequency first second : Space) :
    pairing frequency (first + second) = pairing frequency first * pairing frequency second := by
  unfold pairing
  have equality : (-inner ℝ (first + second).1 frequency.1,
      -(∑ coordinate, frequency.2 coordinate * (first + second).2 coordinate)) =
      (-inner ℝ first.1 frequency.1, -(∑ coordinate, frequency.2 coordinate * first.2 coordinate)) +
      (-inner ℝ second.1 frequency.1, -(∑ coordinate, frequency.2 coordinate * second.2 coordinate)) := by
    apply Prod.ext
    · simp only [Prod.fst_add, inner_add_left, neg_add]
    · simp only [Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
  rw [equality, AdelicCharacter.phase_add]

theorem pairing_neg_mul (frequency value : Space) :
    pairing frequency (-value) * pairing frequency value = 1 := by
  rw [← pairing_add, neg_add_cancel, pairing_zero]

theorem pairing_rational (frequency value : Coordinate → ℚ) :
    pairing (UnitBoxPoisson.rationalPoint frequency) (UnitBoxPoisson.rationalPoint value) = 1 := by
  unfold pairing
  have equality : (-inner ℝ (UnitBoxPoisson.rationalPoint value).1 (UnitBoxPoisson.rationalPoint frequency).1,
      -(∑ coordinate, (UnitBoxPoisson.rationalPoint frequency).2 coordinate *
        (UnitBoxPoisson.rationalPoint value).2 coordinate)) =
      rationalAdele (-(∑ coordinate, frequency coordinate * value coordinate)) := by
    apply Prod.ext
    · change -inner ℝ (WithLp.toLp 2 (fun coordinate => (value coordinate : ℝ)))
          (WithLp.toLp 2 (fun coordinate => (frequency coordinate : ℝ))) =
        ((-(∑ coordinate, frequency coordinate * value coordinate) : ℚ) : ℝ)
      rw [EuclideanSpace.inner_toLp_toLp]
      simp only [dotProduct, Pi.star_apply, star_trivial]
      push_cast
      congr 1
    · change -(∑ coordinate, algebraMap ℚ FiniteAdeles (frequency coordinate) *
          algebraMap ℚ FiniteAdeles (value coordinate)) =
        algebraMap ℚ FiniteAdeles (-(∑ coordinate, frequency coordinate * value coordinate))
      simp only [map_neg, map_sum, map_mul]
  rw [equality, AdelicCharacter.phase_rational]

def translate (function : Space → ℂ) (offset : Space) (value : Space) : ℂ := function (value + offset)

theorem transform_translate (function : Space → ℂ) (offset frequency : Space) :
    transform (translate function offset) frequency =
      pairing frequency (-offset) * transform function frequency := by
  unfold transform translate
  calc
    (∫ value, pairing frequency value * function (value + offset) ∂measure) =
        ∫ value, pairing frequency (-offset) * (pairing frequency (value + offset) * function (value + offset)) ∂measure := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro value
      dsimp only
      rw [pairing_add]
      have factor := pairing_neg_mul frequency offset
      calc
        _ = (pairing frequency (-offset) * pairing frequency offset) *
            (pairing frequency value * function (value + offset)) := by rw [factor, one_mul]
        _ = _ := by ring
    _ = pairing frequency (-offset) *
        ∫ value, pairing frequency (value + offset) * function (value + offset) ∂measure := integral_const_mul _ _
    _ = _ := congrArg (fun value : ℂ => pairing frequency (-offset) * value)
      (integral_add_right_eq_self (fun value => pairing frequency value * function value) offset)

theorem transform_rational_translate (function : Space → ℂ) (offset frequency : Coordinate → ℚ) :
    transform (translate function (UnitBoxPoisson.rationalPoint offset)) (UnitBoxPoisson.rationalPoint frequency) =
      transform function (UnitBoxPoisson.rationalPoint frequency) := by
  rw [transform_translate, ← rationalPoint_neg, pairing_rational, one_mul]

theorem rational_sum_translate (function : Space → ℂ) (offset : Coordinate → ℚ) :
    (∑' rational : Coordinate → ℚ,
      translate function (UnitBoxPoisson.rationalPoint offset) (UnitBoxPoisson.rationalPoint rational)) =
      ∑' rational : Coordinate → ℚ, function (UnitBoxPoisson.rationalPoint rational) := by
  have equality := (Equiv.addRight offset).tsum_eq (fun rational => function (UnitBoxPoisson.rationalPoint rational))
  simpa only [Equiv.coe_addRight, rationalPoint_add, translate] using equality

theorem rational_hasSum_translate (function : Space → ℂ) (offset : Coordinate → ℚ) (sum : ℂ)
    (converges : HasSum (fun value : Coordinate → ℚ => function (UnitBoxPoisson.rationalPoint value)) sum) :
    HasSum (fun value : Coordinate → ℚ =>
      translate function (UnitBoxPoisson.rationalPoint offset) (UnitBoxPoisson.rationalPoint value)) sum := by
  have reindexed := (Equiv.addRight offset).hasSum_iff.mpr converges
  change HasSum (fun value => function (UnitBoxPoisson.rationalPoint (value + offset))) sum at reindexed
  simpa only [rationalPoint_add, translate] using reindexed

theorem poisson_translate (realTest : SchwartzMap RealSpace ℂ) (offset : Coordinate → ℚ) :
    (∑' rational : Coordinate → ℚ,
      translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset)
        (UnitBoxPoisson.rationalPoint rational)) =
      ∑' rational : Coordinate → ℚ,
        transform (translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset))
          (UnitBoxPoisson.rationalPoint rational) := by
  simp only [rational_sum_translate, transform_rational_translate]
  exact UnitBoxPoisson.poisson realTest

theorem poisson_translate_hasSum (realTest : SchwartzMap RealSpace ℂ) (offset : Coordinate → ℚ) :
    HasSum (fun rational : Coordinate → ℚ =>
      transform (translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset))
        (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ,
        translate (tensor realTest UnitBoxPoisson.unitBox) (UnitBoxPoisson.rationalPoint offset)
          (UnitBoxPoisson.rationalPoint rational)) := by
  simp only [transform_rational_translate, rational_sum_translate]
  exact UnitBoxPoisson.poisson_hasSum realTest

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicFourierTranslation
