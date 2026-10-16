module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.SchwartzPoisson
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Schwartz.Regularization

@[expose] public section


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def dilate (test : SchwartzMap RealSpace Target) (scale : ℝˣ) : SchwartzMap RealSpace Target :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (RealFourierScaling.dilation scale) test

theorem dilate_apply (test : SchwartzMap RealSpace Target) (scale : ℝˣ) (value : RealSpace) :
    dilate test scale value = test (scale.val • value) := rfl

def killValue (test : SchwartzMap RealSpace Target) : SchwartzMap RealSpace Target :=
  test - dilate test SchwartzRegularization.scale

def killFourier (test : SchwartzMap RealSpace Target) : SchwartzMap RealSpace Target :=
  test - (64 : ℂ) • dilate test SchwartzRegularization.scale

def regularize (test : SchwartzMap RealSpace Target) : SchwartzMap RealSpace Target := killFourier (killValue test)

theorem postcomp_dilate (test : SchwartzMap RealSpace Target) (functional : Target →L[ℂ] ℂ) (scale : ℝˣ) :
    SchwartzMap.postcompCLM functional (dilate test scale) =
      RealFourierScaling.dilate (SchwartzMap.postcompCLM functional test) scale := by
  ext value
  rfl

theorem postcomp_regularize (test : SchwartzMap RealSpace Target) (functional : Target →L[ℂ] ℂ) :
    SchwartzMap.postcompCLM functional (regularize test) =
      SchwartzRegularization.regularize (SchwartzMap.postcompCLM functional test) := by
  simp only [regularize, killFourier, killValue, map_sub, map_smul, postcomp_dilate,
    SchwartzRegularization.regularize, SchwartzRegularization.killFourier, SchwartzRegularization.killValue]

theorem regularize_zero (test : SchwartzMap RealSpace Target) : regularize test 0 = 0 := by
  simp [regularize, killFourier, killValue, dilate_apply]

theorem regularize_fourier_zero [CompleteSpace Target] (test : SchwartzMap RealSpace Target) :
    FourierTransform.fourier (regularize test) 0 = 0 := by
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro functional
  rw [← BanachSchwartzPoisson.fourier_postcomp, postcomp_regularize]
  exact SchwartzRegularization.regularize_fourier_zero _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization
