module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RectangularFourier

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier

abbrev Space := RealSpace × FiniteRectangularFourier.Space

def measure : Measure Space := (volume : Measure RealSpace).prod FiniteRectangularFourier.measure

def pairing (frequency value : Space) : ℂ :=
  AdelicCharacter.phase (-inner ℝ value.1 frequency.1,
    -(∑ coordinate, frequency.2 coordinate * value.2 coordinate))

theorem pairing_split (frequency value : Space) :
    pairing frequency value = (Real.fourierChar (-inner ℝ value.1 frequency.1) : ℂ) *
      FiniteRectangularFourier.pairing frequency.2 value.2 := AdelicCharacter.phase_apply _

theorem pairing_norm (frequency value : Space) : ‖pairing frequency value‖ = 1 :=
  AdelicCharacter.phase_norm _

def transform (function : Space → ℂ) (frequency : Space) : ℂ :=
  ∫ value, pairing frequency value * function value ∂measure

def tensor (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (value : Space) : ℂ := realTest value.1 * finiteTest value.2

theorem transform_tensor (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (frequency : Space) :
    transform (tensor realTest finiteTest) frequency =
      FourierTransform.fourier realTest frequency.1 * FiniteRectangularFourier.transform finiteTest frequency.2 := by
  unfold transform tensor
  have integrand : (fun value : Space => pairing frequency value * (realTest value.1 * finiteTest value.2)) =
      (fun value : Space => ((Real.fourierChar (-inner ℝ value.1 frequency.1) : ℂ) * realTest value.1) *
        (FiniteRectangularFourier.pairing frequency.2 value.2 * finiteTest value.2)) := by
    funext value
    rw [pairing_split]
    ring
  rw [integrand, measure, integral_prod_mul
    (fun value : RealSpace => (Real.fourierChar (-inner ℝ value frequency.1) : ℂ) * realTest value)
    (fun value : FiniteRectangularFourier.Space => FiniteRectangularFourier.pairing frequency.2 value * finiteTest value)]
  have realEquality := congrFun (SchwartzMap.fourier_coe realTest) frequency.1
  rw [Real.fourier_eq] at realEquality
  change FourierTransform.fourier realTest frequency.1 =
    ∫ value : RealSpace, (Real.fourierChar (-inner ℝ value frequency.1) : ℂ) * realTest value at realEquality
  rw [← realEquality]
  rfl

theorem tensor_integrable (realTest : SchwartzMap RealSpace ℂ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteIntegrable : Integrable finiteTest FiniteRectangularFourier.measure) :
    Integrable (tensor realTest finiteTest) measure :=
  realTest.integrable.mul_prod finiteIntegrable

theorem box_tensor_integrable (realTest : SchwartzMap RealSpace ℂ)
    (scales : Coordinate → FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    Integrable (tensor realTest (FiniteRectangularFourier.boxTest scales offset)) measure :=
  tensor_integrable realTest _ (FiniteRectangularFourier.boxTest_integrable scales offset)

theorem box_transform_integrable (realTest : SchwartzMap RealSpace ℂ)
    (scales : Coordinate → FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space) :
    Integrable (transform (tensor realTest (FiniteRectangularFourier.boxTest scales offset))) measure := by
  have equality : transform (tensor realTest (FiniteRectangularFourier.boxTest scales offset)) =
      tensor (FourierTransform.fourier realTest) (FiniteRectangularFourier.transform (FiniteRectangularFourier.boxTest scales offset)) := by
    funext frequency
    exact transform_tensor _ _ _
  rw [equality]
  exact tensor_integrable _ _ (FiniteRectangularFourier.transform_boxTest_integrable scales offset)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicRectangularFourier
