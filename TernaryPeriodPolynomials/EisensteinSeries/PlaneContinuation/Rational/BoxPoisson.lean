module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Adelic.ScaledPoisson

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRationalScaling TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicFourierTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicScaledPoisson
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalBoxPoisson

def realScale (rational : ℚˣ) : RealSpace ≃L[ℝ] RealSpace :=
  ContinuousLinearEquiv.smulLeft (Units.map (algebraMap ℚ ℝ).toMonoidHom rational)

def adjust (realTest : SchwartzMap RealSpace ℂ) (rational : ℚˣ) (offset : Coordinate → ℚ) :
    SchwartzMap RealSpace ℂ :=
  SchwartzMap.compSubConstCLM ℂ (UnitBoxPoisson.rationalPoint offset).1
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realScale rational).symm realTest)

theorem adjust_apply (realTest : SchwartzMap RealSpace ℂ) (rational : ℚˣ) (offset : Coordinate → ℚ)
    (value : RealSpace) : adjust realTest rational offset
      ((rational.val : ℝ) • value + (UnitBoxPoisson.rationalPoint offset).1) = realTest value := by
  rw [adjust, SchwartzMap.compSubConstCLM_apply, add_sub_cancel_right,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change realTest ((realScale rational).symm (realScale rational value)) = realTest value
  rw [ContinuousLinearEquiv.symm_apply_apply]

def rationalOffset (scale : ℚˣ) (offset : FiniteRectangularFourier.Space) : Coordinate → ℚ :=
  fun coordinate => -FiniteAdditiveClass.rationalPart
    ((FiniteLatticeMeasure.rationalScale scale).inv * offset coordinate)

theorem offset_integral (scale : ℚˣ) (offset : FiniteRectangularFourier.Space) (coordinate : Coordinate) :
    (FiniteLatticeMeasure.rationalScale scale).inv * offset coordinate +
      algebraMap ℚ FiniteAdeles (rationalOffset scale offset coordinate) ∈ Set.range integralEmbedding := by
  let value := (FiniteLatticeMeasure.rationalScale scale).inv * offset coordinate
  refine ⟨FiniteAdditiveClass.integralPart value, ?_⟩
  change integralEmbedding (FiniteAdditiveClass.integralPart value) = value +
    algebraMap ℚ FiniteAdeles (-FiniteAdditiveClass.rationalPart value)
  rw [map_neg]
  linear_combination -(FiniteAdditiveClass.decomposition value)

theorem affine_integral_iff (scale : ℚˣ) (offset value : FiniteRectangularFourier.Space) (coordinate : Coordinate) :
    (FiniteLatticeMeasure.rationalScale scale).inv * value coordinate +
        algebraMap ℚ FiniteAdeles (rationalOffset scale offset coordinate) ∈ Set.range integralEmbedding ↔
      value coordinate ∈ FiniteFourier.coset (FiniteLatticeMeasure.rationalScale scale) (offset coordinate) := by
  rw [FiniteFourierInversion.coset_mem, FiniteFourierInversion.lattice_mem]
  have constantZero := (FiniteAdditiveClass.class_kernel _).mpr (offset_integral scale offset coordinate)
  have equality : (FiniteLatticeMeasure.rationalScale scale).inv * value coordinate +
      algebraMap ℚ FiniteAdeles (rationalOffset scale offset coordinate) =
      (value coordinate - offset coordinate) * (FiniteLatticeMeasure.rationalScale scale).inv +
        ((FiniteLatticeMeasure.rationalScale scale).inv * offset coordinate +
          algebraMap ℚ FiniteAdeles (rationalOffset scale offset coordinate)) := by ring
  rw [equality, ← FiniteAdditiveClass.class_kernel, ← FiniteAdditiveClass.class_kernel,
    map_add, constantZero, add_zero]

theorem finite_test_identity (scale : ℚˣ) (offset value : FiniteRectangularFourier.Space) :
    UnitBoxPoisson.unitBox (fun coordinate =>
      (FiniteLatticeMeasure.rationalScale scale).inv * value coordinate +
        algebraMap ℚ FiniteAdeles (rationalOffset scale offset coordinate)) =
      FiniteRectangularFourier.boxTest (fun _ => FiniteLatticeMeasure.rationalScale scale) offset value := by
  unfold UnitBoxPoisson.unitBox FiniteRectangularFourier.boxTest FiniteRectangularFourier.tensor
  apply Finset.prod_congr rfl
  intro coordinate _
  dsimp only
  change (FiniteFourier.coset 1 0).indicator (fun _ => (1 : ℂ)) _ = _
  rw [UnitBoxPoisson.unit_coset]
  by_cases membership : value coordinate ∈ FiniteFourier.coset (FiniteLatticeMeasure.rationalScale scale) (offset coordinate)
  · rw [Set.indicator_of_mem ((affine_integral_iff scale offset value coordinate).mpr membership),
      Set.indicator_of_mem membership]
  · rw [Set.indicator_of_notMem (fun h => membership ((affine_integral_iff scale offset value coordinate).mp h)),
      Set.indicator_of_notMem membership]

theorem tensor_identity (realTest : SchwartzMap RealSpace ℂ) (scale : ℚˣ) (offset : FiniteRectangularFourier.Space) :
    tensor realTest (FiniteRectangularFourier.boxTest (fun _ => FiniteLatticeMeasure.rationalScale scale) offset) =
      dilate (translate (tensor (adjust realTest scale⁻¹ (rationalOffset scale offset)) UnitBoxPoisson.unitBox)
        (UnitBoxPoisson.rationalPoint (rationalOffset scale offset))) scale⁻¹ := by
  funext value
  unfold dilate translate tensor
  change realTest value.1 * _ = adjust realTest scale⁻¹ (rationalOffset scale offset)
    ((((scale⁻¹).val : ℝ) • value.1) + (UnitBoxPoisson.rationalPoint (rationalOffset scale offset)).1) * _
  rw [adjust_apply]
  congr 1
  exact (finite_test_identity scale offset value.2).symm

theorem poisson (realTest : SchwartzMap RealSpace ℂ) (scale : ℚˣ) (offset : FiniteRectangularFourier.Space) :
    (∑' rational : Coordinate → ℚ,
      tensor realTest (FiniteRectangularFourier.boxTest (fun _ => FiniteLatticeMeasure.rationalScale scale) offset)
        (UnitBoxPoisson.rationalPoint rational)) =
      ∑' rational : Coordinate → ℚ,
        transform (tensor realTest (FiniteRectangularFourier.boxTest (fun _ => FiniteLatticeMeasure.rationalScale scale) offset))
          (UnitBoxPoisson.rationalPoint rational) := by
  rw [tensor_identity]
  exact poisson_dilate_translate _ _ _

theorem poisson_hasSum (realTest : SchwartzMap RealSpace ℂ) (scale : ℚˣ) (offset : FiniteRectangularFourier.Space) :
    HasSum (fun rational : Coordinate → ℚ =>
      transform (tensor realTest (FiniteRectangularFourier.boxTest (fun _ => FiniteLatticeMeasure.rationalScale scale) offset))
        (UnitBoxPoisson.rationalPoint rational))
      (∑' rational : Coordinate → ℚ,
        tensor realTest (FiniteRectangularFourier.boxTest (fun _ => FiniteLatticeMeasure.rationalScale scale) offset)
          (UnitBoxPoisson.rationalPoint rational)) := by
  rw [tensor_identity]
  exact poisson_dilate_translate_hasSum _ _ _

theorem summable (realTest : SchwartzMap RealSpace ℂ) (scale : ℚˣ) (offset : FiniteRectangularFourier.Space) :
    Summable (fun rational : Coordinate → ℚ =>
      tensor realTest (FiniteRectangularFourier.boxTest (fun _ => FiniteLatticeMeasure.rationalScale scale) offset)
        (UnitBoxPoisson.rationalPoint rational)) := by
  rw [tensor_identity]
  exact (dilate_translate_hasSum _ _ _).summable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalBoxPoisson
