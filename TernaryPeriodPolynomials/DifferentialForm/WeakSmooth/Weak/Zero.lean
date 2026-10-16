module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.OnePoincare

@[expose] public section


/-! Actual zero-gradient rigidity passes from a base domain to a product cylinder. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every literal weak directional derivative of this current vanishes. -/
def HasZeroWeakDerivative (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) : Prop :=
  ∀ v, scalarWeakDerivative Ω v T = 0

/-- Zero-gradient currents are scalar multiples of the specified actual mass current. -/
def ScalarWeakZeroRigid (Ω : TopologicalSpace.Opens E) (I : ScalarWeak Ω) : Prop :=
  ∀ T : ScalarWeak Ω, HasZeroWeakDerivative Ω T → ∃ c : ℝ, T = c • I

variable [FiniteDimensional ℝ E]

/-- The actual fiber factorization gives zero-gradient rigidity on a cylinder. -/
theorem scalarWeakZeroRigid_cylinder (Ω : TopologicalSpace.Opens E) (I : ScalarWeak Ω)
    (hΩ : ScalarWeakZeroRigid Ω I) :
    ScalarWeakZeroRigid (testCylinder Ω) (weakFiberLift Ω I) := by
  intro T hT
  have hbase : HasZeroWeakDerivative Ω (weakFiberRestriction Ω T) := by
    intro v
    rw [← weakFiberRestriction_horizontal_derivative, hT (v, 0), map_zero]
  obtain ⟨c, hc⟩ := hΩ (weakFiberRestriction Ω T) hbase
  refine ⟨c, ?_⟩
  rw [weakFiberLift_of_last_derivative_zero Ω T (hT (0, 1)), hc, map_smul]

/-- Lifting an actual zero-gradient current preserves vanishing of every directional derivative. -/
theorem weakFiberLift_hasZeroWeakDerivative (Ω : TopologicalSpace.Opens E)
    (I : ScalarWeak Ω) (hI : HasZeroWeakDerivative Ω I) :
    HasZeroWeakDerivative (testCylinder Ω) (weakFiberLift Ω I) := by
  intro p
  have hp : p = (p.1, 0) + p.2 • ((0 : E), (1 : ℝ)) := by ext <;> simp
  change scalarWeakGradient (testCylinder Ω) (weakFiberLift Ω I) p = 0
  rw [hp, map_add, map_smul]
  change scalarWeakDerivative (testCylinder Ω) (p.1, 0) (weakFiberLift Ω I) +
    p.2 • scalarWeakDerivative (testCylinder Ω) (0, 1) (weakFiberLift Ω I) = 0
  rw [weakFiberLift_horizontal_derivative, hI, map_zero, weakFiberLift_last_derivative,
    smul_zero, add_zero]

end TernaryPoly.PolynomialFormWeakSmooth
