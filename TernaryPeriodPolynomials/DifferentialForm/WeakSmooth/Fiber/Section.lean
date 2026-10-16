module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.Integral

@[expose] public section


/-! A genuine normalized compact-test section of product fiber integration. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped ContDiff Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Multiplication by the fixed unit-mass test in the final coordinate. -/
def fiberTestSectionRaw (f : E → ℝ) (p : E × ℝ) : ℝ := f p.1 * unitTest p.2

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem fiberTestSectionRaw_tsupport {f : E → ℝ} :
    tsupport (fiberTestSectionRaw f) ⊆ tsupport f ×ˢ tsupport unitTest := by
  apply closure_minimal _ ((isClosed_tsupport f).prod (isClosed_tsupport unitTest))
  intro p hp
  have h : f p.1 ≠ 0 ∧ unitTest p.2 ≠ 0 := mul_ne_zero_iff.mp hp
  exact ⟨subset_tsupport f h.1, subset_tsupport unitTest h.2⟩

/-- This section preserves the actual compact smooth test condition. -/
def fiberTestSection (Ω : TopologicalSpace.Opens E) :
    𝓓(Ω, ℝ) →ₗ[ℝ] 𝓓(testCylinder Ω, ℝ) where
  toFun f :=
    { toFun := fiberTestSectionRaw f
      contDiff' := (f.contDiff.comp contDiff_fst).mul (unitTest.contDiff.comp contDiff_snd)
      hasCompactSupport' := (f.hasCompactSupport.prod unitTest.hasCompactSupport).of_isClosed_subset
        (isClosed_tsupport _) fiberTestSectionRaw_tsupport
      tsupport_subset' := by
        intro p hp
        have h := fiberTestSectionRaw_tsupport hp
        exact ⟨f.tsupport_subset h.1, unitTest.tsupport_subset h.2⟩ }
  map_add' f g := by
    apply TestFunction.ext
    intro p
    exact add_mul _ _ _
  map_smul' c f := by
    apply TestFunction.ext
    intro p
    exact mul_assoc c (f p.1) (unitTest p.2)

omit [FiniteDimensional ℝ E] in
@[simp] theorem fiberTestSection_apply (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(Ω, ℝ)) (p : E × ℝ) : fiberTestSection Ω f p = f p.1 * unitTest p.2 := rfl

/-- Fiber integration followed by the fixed normalized tensor insertion is the identity. -/
theorem fiberTestIntegral_section (Ω : TopologicalSpace.Opens E) (f : 𝓓(Ω, ℝ)) :
    fiberTestIntegral Ω (fiberTestSection Ω f) = f := by
  apply TestFunction.ext
  intro x
  change (∫ t in (0 : ℝ)..1, f x * unitTest t) = f x
  rw [intervalIntegral.integral_const_mul, unitTest_intervalIntegral, mul_one]

end TernaryPoly.PolynomialFormWeakSmooth
