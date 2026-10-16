module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.ScalarWeak

@[expose] public section


/-! Actual weak one-forms and their literal scalar weak gradients. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A weak one-form is a linear directional family of actual scalar test currents. -/
abbrev ScalarWeakOne (Ω : TopologicalSpace.Opens E) := E →ₗ[ℝ] ScalarWeak Ω

/-- The actual weak gradient is linear in the tangent direction. -/
def scalarWeakGradient (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) : ScalarWeakOne Ω where
  toFun v := scalarWeakDerivative Ω v T
  map_add' u v := by
    apply LinearMap.ext
    intro f
    simp only [scalarWeakDerivative_apply, TestFunction.lineDerivCLM_add,
      _root_.add_apply, map_add, neg_add, LinearMap.add_apply]
  map_smul' c v := by
    apply LinearMap.ext
    intro f
    simp only [scalarWeakDerivative_apply, TestFunction.lineDerivCLM_smul,
      _root_.smul_apply, map_smul, LinearMap.smul_apply,
      RingHom.id_apply, smul_neg]

@[simp] theorem scalarWeakGradient_apply (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak Ω) (v : E) : scalarWeakGradient Ω T v = scalarWeakDerivative Ω v T := rfl

/-- Literal equality of the two mixed weak directional derivatives. -/
def IsClosedScalarWeakOne (Ω : TopologicalSpace.Opens E) (w : ScalarWeakOne Ω) : Prop :=
  ∀ u v, scalarWeakDerivative Ω u (w v) = scalarWeakDerivative Ω v (w u)

theorem scalarWeakGradient_closed (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) :
    IsClosedScalarWeakOne Ω (scalarWeakGradient Ω T) :=
  scalarWeakDerivative_commute Ω T

/-- Exactness of actual closed scalar weak one-forms on this specific open set. -/
def ScalarWeakOneExact (Ω : TopologicalSpace.Opens E) : Prop :=
  ∀ w : ScalarWeakOne Ω, IsClosedScalarWeakOne Ω w →
    ∃ T : ScalarWeak Ω, scalarWeakGradient Ω T = w

end TernaryPoly.PolynomialFormWeakSmooth
