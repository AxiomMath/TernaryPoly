module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.BoxPoisson

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSumPoisson

theorem pairing_continuous (frequency : Space) : Continuous (pairing frequency) := by
  have equality : pairing frequency = fun value : Space =>
      (Real.fourierChar (-inner ℝ value.1 frequency.1) : ℂ) *
        FiniteRectangularFourier.pairing frequency.2 value.2 := funext (pairing_split frequency)
  rw [equality]
  exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_fst.inner continuous_const).neg)).mul
    ((FiniteRectangularFourier.pairing_continuous frequency.2).comp continuous_snd)

theorem weighted_integrable (function : Space → ℂ) (integrable : Integrable function measure) (frequency : Space) :
    Integrable (fun value => pairing frequency value * function value) measure :=
  integrable.bdd_mul (pairing_continuous frequency).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun value => (pairing_norm frequency value).le))

theorem transform_sum {Index : Type*} (indices : Finset Index) (functions : Index → Space → ℂ)
    (integrable : ∀ index ∈ indices, Integrable (functions index) measure) (frequency : Space) :
    transform (fun value => ∑ index ∈ indices, functions index value) frequency =
      ∑ index ∈ indices, transform (functions index) frequency := by
  unfold transform
  simp only [Finset.mul_sum]
  exact integral_finsetSum indices (fun index membership => weighted_integrable _ (integrable index membership) frequency)

theorem transform_const_mul (scalar : ℂ) (function : Space → ℂ) (frequency : Space) :
    transform (fun value => scalar * function value) frequency = scalar * transform function frequency := by
  unfold transform
  have equality : (fun value => pairing frequency value * (scalar * function value)) =
      fun value => scalar * (pairing frequency value * function value) := by
    funext value
    ring
  rw [equality, integral_const_mul]

theorem poisson_sum_hasSum {Index : Type*} (indices : Finset Index) (functions : Index → Space → ℂ)
    (integrable : ∀ index ∈ indices, Integrable (functions index) measure)
    (summable : ∀ index ∈ indices, Summable (fun rational : Coordinate → ℚ => functions index (UnitBoxPoisson.rationalPoint rational)))
    (poisson : ∀ index ∈ indices, HasSum
      (fun rational : Coordinate → ℚ => transform (functions index) (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ, functions index (UnitBoxPoisson.rationalPoint rational))) :
    HasSum (fun rational : Coordinate → ℚ =>
      transform (fun value => ∑ index ∈ indices, functions index value) (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ, ∑ index ∈ indices, functions index (UnitBoxPoisson.rationalPoint rational)) := by
  simp only [transform_sum indices functions integrable]
  rw [Summable.tsum_finsetSum summable]
  exact hasSum_sum poisson

theorem poisson_const_mul_hasSum (function : Space → ℂ) (scalar : ℂ)
    (poisson : HasSum (fun rational : Coordinate → ℚ => transform function (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ, function (UnitBoxPoisson.rationalPoint rational))) :
    HasSum (fun rational : Coordinate → ℚ =>
      transform (fun value => scalar * function value) (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ, scalar * function (UnitBoxPoisson.rationalPoint rational)) := by
  simp only [transform_const_mul, tsum_mul_left]
  exact poisson.mul_left scalar

theorem boxes_poisson_hasSum {Index : Type*} (indices : Finset Index)
    (realTests : Index → SchwartzMap RealSpace ℂ) (scales : Index → ℚˣ)
    (offsets : Index → FiniteRectangularFourier.Space) :
    HasSum (fun rational : Coordinate → ℚ =>
      transform (fun value => ∑ index ∈ indices,
        tensor (realTests index) (FiniteRectangularFourier.boxTest
          (fun _ => FiniteLatticeMeasure.rationalScale (scales index)) (offsets index)) value)
        (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ, ∑ index ∈ indices,
        tensor (realTests index) (FiniteRectangularFourier.boxTest
          (fun _ => FiniteLatticeMeasure.rationalScale (scales index)) (offsets index))
          (UnitBoxPoisson.rationalPoint rational)) :=
  poisson_sum_hasSum indices _ (fun _ _ => box_tensor_integrable _ _ _)
    (fun index _ => RationalBoxPoisson.summable (realTests index) (scales index) (offsets index))
    (fun index _ => RationalBoxPoisson.poisson_hasSum (realTests index) (scales index) (offsets index))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteSumPoisson
