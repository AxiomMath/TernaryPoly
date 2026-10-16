module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Godement.RealScaling

@[expose] public section


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzRegularization

def scale : ℝˣ := Units.mk0 2 (by norm_num)

def killValue (test : SchwartzMap RealSpace ℂ) : SchwartzMap RealSpace ℂ :=
  test - RealFourierScaling.dilate test scale

def killFourier (test : SchwartzMap RealSpace ℂ) : SchwartzMap RealSpace ℂ :=
  test - (64 : ℂ) • RealFourierScaling.dilate test scale

def regularize (test : SchwartzMap RealSpace ℂ) : SchwartzMap RealSpace ℂ := killFourier (killValue test)

theorem scale_pos : 0 < scale.val := by norm_num [scale]

theorem factor : RealFourierScaling.factor scale = 1 / 64 := by
  norm_num [RealFourierScaling.factor, scale]

theorem killValue_zero (test : SchwartzMap RealSpace ℂ) : killValue test 0 = 0 := by
  simp [killValue, RealFourierScaling.dilate_apply]

theorem killFourier_zero (test : SchwartzMap RealSpace ℂ) (vanishing : test 0 = 0) : killFourier test 0 = 0 := by
  simp [killFourier, RealFourierScaling.dilate_apply, vanishing]

theorem killFourier_fourier_zero (test : SchwartzMap RealSpace ℂ) : FourierTransform.fourier (killFourier test) 0 = 0 := by
  simp only [killFourier, sub_eq_add_neg, FourierAdd.fourier_add, FourierTransform.fourier_neg,
    FourierSMul.fourier_smul, add_apply, neg_apply, smul_apply,
    RealFourierScaling.fourier_dilate, smul_zero, factor, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

theorem regularize_zero (test : SchwartzMap RealSpace ℂ) : regularize test 0 = 0 :=
  killFourier_zero _ (killValue_zero test)

theorem regularize_fourier_zero (test : SchwartzMap RealSpace ℂ) : FourierTransform.fourier (regularize test) 0 = 0 :=
  killFourier_fourier_zero _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SchwartzRegularization
