module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Derivative

@[expose] public section


/-! Actual vector-valued weak one-form Poincare from the proved scalar compact-test theorem. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E V I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup V] [Module ℝ V]

/-- Evaluate a vector-valued weak one-form by an actual constant coefficient functional. -/
def weakOneCoefficient (Ω : TopologicalSpace.Opens E) (L : V →ₗ[ℝ] ℝ)
    (w : E →ₗ[ℝ] ValuedWeak (V := V) Ω) : ScalarWeakOne Ω where
  toFun v := L.comp (w v)
  map_add' u v := by
    apply LinearMap.ext
    intro φ
    change L ((w (u + v)) φ) = L ((w u) φ) + L ((w v) φ)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' c v := by
    apply LinearMap.ext
    intro φ
    change L ((w (c • v)) φ) = c • L ((w v) φ)
    rw [map_smul, LinearMap.smul_apply, map_smul]

/-- Actual scalar coefficients of an actual closed vector-valued weak one-form are closed. -/
theorem weakOneCoefficient_closed (Ω : TopologicalSpace.Opens E) (L : V →ₗ[ℝ] ℝ)
    (w : E →ₗ[ℝ] ValuedWeak (V := V) Ω)
    (hw : ∀ u v, valuedWeakDerivative Ω u (w v) = valuedWeakDerivative Ω v (w u)) :
    IsClosedScalarWeakOne Ω (weakOneCoefficient Ω L w) := by
  intro u v
  change valuedWeakDerivative Ω u (L.comp (w v)) = valuedWeakDerivative Ω v (L.comp (w u))
  rw [valuedWeakDerivative_comp, valuedWeakDerivative_comp, hw]

/-- If actual scalar weak one-forms are exact on Ω, the same is true with any real coefficient
space possessing a genuine finite-coordinate linear equivalence. -/
theorem valuedWeakOneExact_of_scalar (Ω : TopologicalSpace.Opens E)
    (hΩ : ScalarWeakOneExact Ω) (e : V ≃ₗ[ℝ] (I → ℝ))
    (w : E →ₗ[ℝ] ValuedWeak (V := V) Ω)
    (hw : ∀ u v, valuedWeakDerivative Ω u (w v) = valuedWeakDerivative Ω v (w u)) :
    ∃ T : ValuedWeak (V := V) Ω, valuedWeakGradient Ω T = w := by
  have hex (i : I) : ∃ T : ScalarWeak Ω,
      scalarWeakGradient Ω T = weakOneCoefficient Ω ((LinearMap.proj i).comp e.toLinearMap) w :=
    hΩ _ (weakOneCoefficient_closed Ω _ w hw)
  choose T hT using hex
  refine ⟨e.symm.toLinearMap.comp (LinearMap.pi T), ?_⟩
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro φ
  apply e.injective
  funext i
  have hi := congrArg (fun W : ScalarWeakOne Ω => W v φ) (hT i)
  change -T i (TestFunction.lineDerivCLM ℝ v φ) = e (w v φ) i at hi
  change e (-e.symm (fun j => T j (TestFunction.lineDerivCLM ℝ v φ))) i = e (w v φ) i
  rw [map_neg, e.apply_symm_apply]
  exact hi

end TernaryPoly.PolynomialFormWeakSmooth
