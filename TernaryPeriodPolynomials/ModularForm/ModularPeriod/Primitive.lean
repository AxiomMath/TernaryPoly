module

public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Linear
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Algebra.Order.Field.Pointwise
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section


noncomputable section
open Complex
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspPeriod

/-- The actual scalar-valued differential underlying evaluation of the full period polynomial. -/
def periodIntegrand {d : ℕ} (f : Forms d) (x y z : ℂ) : ℂ :=
  f (ofComplex z) * (z*y-x)^d

/-- The actual period integrand is holomorphic throughout the open upper half plane. -/
theorem periodIntegrand_differentiableOn {d : ℕ} (f : Forms d) (x y : ℂ) :
    DifferentiableOn ℂ (periodIntegrand f x y) {z : ℂ | 0 < z.im} := by
  exact (UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)).mul
    (((differentiable_id.mul_const y).sub_const x).pow d).differentiableOn

/-- The actual period differential admits a holomorphic primitive on the entire upper half plane.
This handles finite paths; cusp-endpoint limits remain a separate theorem. -/
theorem exists_period_primitive {d : ℕ} (f : Forms d) (x y : ℂ) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodIntegrand f x y z) z := by
  obtain ⟨F, hF⟩ := (convex_halfSpace_im_gt 0).exists_forall_hasDerivWithinAt
    (periodIntegrand_differentiableOn f x y)
  exact ⟨F, fun z hz => (hF z hz).hasDerivAt (isOpen_upperHalfPlaneSet.mem_nhds hz)⟩

end TernaryPoly.BinaryCuspPeriod
