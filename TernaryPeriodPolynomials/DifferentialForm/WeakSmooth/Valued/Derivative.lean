module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.One

@[expose] public section


/-! Literal weak derivatives of actual compact-test currents with arbitrary real vector-space values. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup V] [Module ℝ V]

/-- A vector-valued algebraic current on actual compact smooth scalar tests. -/
abbrev ValuedWeak (Ω : TopologicalSpace.Opens E) := 𝓓(Ω, ℝ) →ₗ[ℝ] V

/-- The actual weak derivative is minus transposed compact-test differentiation. -/
def valuedWeakDerivative (Ω : TopologicalSpace.Opens E) (v : E) (T : ValuedWeak (V := V) Ω) :
    ValuedWeak (V := V) Ω :=
  -(T.comp (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v).toLinearMap)

@[simp] theorem valuedWeakDerivative_apply (Ω : TopologicalSpace.Opens E) (v : E)
    (T : ValuedWeak (V := V) Ω) (φ : 𝓓(Ω, ℝ)) :
    valuedWeakDerivative Ω v T φ = -T (TestFunction.lineDerivCLM ℝ v φ) := rfl

/-- Actual mixed weak derivatives commute for arbitrary real vector-space-valued test currents. -/
theorem valuedWeakDerivative_commute (Ω : TopologicalSpace.Opens E) (u v : E)
    (T : ValuedWeak (V := V) Ω) :
    valuedWeakDerivative Ω u (valuedWeakDerivative Ω v T) =
      valuedWeakDerivative Ω v (valuedWeakDerivative Ω u T) := by
  apply LinearMap.ext
  intro φ
  simp only [valuedWeakDerivative_apply, neg_neg]
  rw [testDerivative_commute Ω φ v u]

/-- A constant coefficient linear map commutes exactly with the actual weak derivative. -/
theorem valuedWeakDerivative_comp {W : Type} [AddCommGroup W] [Module ℝ W]
    (Ω : TopologicalSpace.Opens E) (L : V →ₗ[ℝ] W) (v : E) (T : ValuedWeak (V := V) Ω) :
    valuedWeakDerivative Ω v (L.comp T) = L.comp (valuedWeakDerivative Ω v T) := by
  apply LinearMap.ext
  intro φ
  simp only [valuedWeakDerivative_apply, LinearMap.comp_apply, map_neg]

/-- The vector-valued weak gradient as a linear function of the actual tangent direction. -/
def valuedWeakGradient (Ω : TopologicalSpace.Opens E) (T : ValuedWeak (V := V) Ω) :
    E →ₗ[ℝ] ValuedWeak (V := V) Ω where
  toFun v := valuedWeakDerivative Ω v T
  map_add' u v := by
    apply LinearMap.ext
    intro φ
    simp only [valuedWeakDerivative_apply, LinearMap.add_apply,
      TestFunction.lineDerivCLM_add, _root_.add_apply, map_add, neg_add]
  map_smul' c v := by
    apply LinearMap.ext
    intro φ
    simp only [valuedWeakDerivative_apply, LinearMap.smul_apply,
      TestFunction.lineDerivCLM_smul, _root_.smul_apply, map_smul, smul_neg]
    rfl

end TernaryPoly.PolynomialFormWeakSmooth
