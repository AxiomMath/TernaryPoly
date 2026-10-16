module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.SchwartzBounds
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Banach.SchwartzRegularization

@[expose] public section


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachSchwartzRegularization

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RegularizedTestFamilies

variable {Target : Type} [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def operator : SchwartzMap RealSpace Target →L[ℂ] SchwartzMap RealSpace Target :=
  let scaling := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := Target)
    (RealFourierScaling.dilation SchwartzRegularization.scale)
  ((ContinuousLinearMap.id ℂ _) - (64 : ℂ) • scaling).comp ((ContinuousLinearMap.id ℂ _) - scaling)

theorem operator_apply (test : SchwartzMap RealSpace Target) : operator test = regularize test := rfl

theorem bounded (tests : Set (SchwartzMap RealSpace Target)) (bounded : UniformSchwartzBounds.Bounded tests) :
    UniformSchwartzBounds.Bounded (regularize '' tests) :=
  UniformSchwartzBounds.image operator tests bounded

theorem family_bounded (tests : ℂ → SchwartzMap RealSpace Target) (parameters : Set ℂ)
    (bounded : UniformSchwartzBounds.Bounded (tests '' parameters)) :
    UniformSchwartzBounds.Bounded ((fun parameter => regularize (tests parameter)) '' parameters) := by
  have result := RegularizedTestFamilies.bounded (tests '' parameters) bounded
  simpa only [Set.image_image] using result

theorem pointwise_differentiable (tests : ℂ → SchwartzMap RealSpace Target)
    (holomorphic : ∀ vector, Differentiable ℂ (fun parameter => tests parameter vector)) (vector : RealSpace) :
    Differentiable ℂ (fun parameter => regularize (tests parameter) vector) := by
  simp only [regularize, killFourier, killValue, _root_.sub_apply, _root_.smul_apply, dilate_apply]
  exact (holomorphic vector |>.sub (holomorphic _)).sub
    ((holomorphic _ |>.sub (holomorphic _)).const_smul (64 : ℂ))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RegularizedTestFamilies
