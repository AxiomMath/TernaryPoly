module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularCurrent
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.One

@[expose] public section


/-! Genuine domain restriction of scalar currents by extension of actual compact smooth tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact test on a smaller actual open domain is the same globally smooth function when
regarded as a test on the larger domain. -/
def scalarTestExtension (Ω U : TopologicalSpace.Opens E) (h : Ω ≤ U) : 𝓓(Ω, ℝ) →ₗ[ℝ] 𝓓(U, ℝ) where
  toFun φ := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem scalarTestExtension_apply (Ω U : TopologicalSpace.Opens E) (h : Ω ≤ U)
    (φ : 𝓓(Ω, ℝ)) (x : E) : scalarTestExtension Ω U h φ x = φ x := rfl

theorem scalarTestExtension_derivative (Ω U : TopologicalSpace.Opens E) (h : Ω ≤ U)
    (φ : 𝓓(Ω, ℝ)) (v : E) :
    scalarTestExtension Ω U h (TestFunction.lineDerivCLM ℝ v φ) =
      TestFunction.lineDerivCLM ℝ v (scalarTestExtension Ω U h φ) := by
  apply TestFunction.ext
  intro x
  simp only [scalarTestExtension_apply,
    TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp)]
  rfl

/-- Literal restriction of algebraic scalar currents is transpose extension of actual tests. -/
def scalarWeakRestriction (Ω U : TopologicalSpace.Opens E) (h : Ω ≤ U) :
    ScalarWeak U →ₗ[ℝ] ScalarWeak Ω := (scalarTestExtension Ω U h).dualMap

@[simp] theorem scalarWeakRestriction_apply (Ω U : TopologicalSpace.Opens E) (h : Ω ≤ U)
    (T : ScalarWeak U) (φ : 𝓓(Ω, ℝ)) :
    scalarWeakRestriction Ω U h T φ = T (scalarTestExtension Ω U h φ) := rfl

theorem scalarWeakRestriction_refl (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) :
    scalarWeakRestriction Ω Ω le_rfl T = T := by
  ext φ
  rfl

theorem scalarWeakRestriction_trans (Ω U V : TopologicalSpace.Opens E) (h : Ω ≤ U) (k : U ≤ V)
    (T : ScalarWeak V) :
    scalarWeakRestriction Ω U h (scalarWeakRestriction U V k T) =
      scalarWeakRestriction Ω V (h.trans k) T := by
  ext φ
  rfl

/-- Actual weak differentiation commutes with actual restriction to a smaller domain. -/
theorem scalarWeakRestriction_derivative (Ω U : TopologicalSpace.Opens E) (h : Ω ≤ U)
    (T : ScalarWeak U) (v : E) :
    scalarWeakRestriction Ω U h (scalarWeakDerivative U v T) =
      scalarWeakDerivative Ω v (scalarWeakRestriction Ω U h T) := by
  apply LinearMap.ext
  intro φ
  simp only [scalarWeakRestriction_apply, scalarWeakDerivative_apply, scalarTestExtension_derivative]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsLocallyFiniteMeasure μ]

/-- Genuine scalar function currents restrict to their actual local coefficient functions. -/
theorem scalarWeakRestriction_regular (Ω U : TopologicalSpace.Opens E) (h : Ω ≤ U)
    (f : E → ℝ) (hf : ContinuousOn f U) :
    scalarWeakRestriction Ω U h (scalarRegularCurrent μ U f hf) =
      scalarRegularCurrent μ Ω f (hf.mono h) := by
  ext φ
  rfl

end TernaryPoly.PolynomialFormWeakSmooth
